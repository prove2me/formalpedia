-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_globally_observable_bounded_vector_estimator
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T20:11:31.463976+00:00
-- url     : https://prove2.me/submissions/61c8aba1-405f-458d-b528-11025a8fb3a5

import Theorems.Thm_BanditAlgorithm_partial_monitoring_pareto_monotone_neighbour_paths
import Definitions.Def_PartialMonitoringAlgorithm26

set_option autoImplicit false

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

private lemma fin_sum_consecutive_sub_global {n : ℕ} (g : Fin (n + 1) → ℝ) :
    ∑ t : Fin n, (g t.castSucc - g t.succ) = g 0 - g (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun t : Fin (n + 1) => g t.succ)
      have htail' : ∑ i : Fin n, (g i.succ.castSucc - g i.succ.succ) =
          g (Fin.succ 0) - g (Fin.last n).succ := by
        calc
          _ = ∑ i : Fin n, (g i.castSucc.succ - g i.succ.succ) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 2
          _ = _ := htail
      rw [htail']
      have hz : g (Fin.castSucc 0) = g 0 := by congr
      have hl : g (Fin.last n).succ = g (Fin.last (n + 1)) := by congr
      rw [hz, hl]
      ring

theorem globally_observable_bounded_vector_estimator
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hglo : GloballyObservable G) :
    ∃ S : Finset (Fin k), ∃ V : ℝ,
      S.Nonempty ∧ 0 ≤ V ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∃ f : Fin k → 𝕊 → Fin k → ℝ,
        PMVectorEstimatorOn G S f ∧ ∀ a σ b, |f a σ b| ≤ V := by
  classical
  obtain ⟨S, hSne, hbest, hpaths⟩ :=
    partial_monitoring_pareto_monotone_neighbour_paths G hk hd
  let lam : Fin d → ℝ := fun _ => 1 / d
  have hlam : lam ∈ stdSimplex ℝ (Fin d) := by
    constructor
    · intro i
      dsimp [lam]
      positivity
    · simp [lam, hd.ne']
  obtain ⟨root, hrootS, hrootpaths⟩ := hpaths lam hlam
  let edge : Fin k → Fin k → Fin k → 𝕊 → ℝ := fun x y =>
    if h : NeighbouringActions G x y then
      fun a σ => Classical.choose (hglo x y h) (a, σ)
    else 0
  have hedge (x y : Fin k) (hxy : NeighbouringActions G x y) :
      IsGlobalLossEstimator G x y (fun z => edge x y z.1 z.2) := by
    dsimp [edge]
    rw [dif_pos hxy]
    exact Classical.choose_spec (hglo x y hxy)
  let M : ℝ := ∑ x : Fin k, ∑ y : Fin k, ∑ a : Fin k, ∑ σ : 𝕊,
    |edge x y a σ|
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let V : ℝ := (k : ℝ) * M
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hV : 0 ≤ V := mul_nonneg hk0 hM
  let B := {b : Fin k // b ∈ S}
  have hpaths' : ∀ b : B,
      ∃ m : ℕ, ∃ path : Fin (m + 1) → Fin k,
        m ≤ k ∧ path 0 = b.1 ∧ path (Fin.last m) = root ∧
        (∀ t, path t ∈ S) ∧
        ∀ t : Fin m, NeighbouringActions G (path t.castSucc) (path t.succ) := by
    intro b
    obtain ⟨m, path, hm, hfirst, hlast, hmem, hstep⟩ := hrootpaths b.1 b.2
    exact ⟨m, path, hm, hfirst, hlast, hmem, fun t => (hstep t).1⟩
  choose m path hm hfirst hlast hpathS hpath using hpaths'
  let f : Fin k → 𝕊 → Fin k → ℝ := fun a σ b =>
    if hb : b ∈ S then ∑ t : Fin (m ⟨b, hb⟩),
      edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ else 0
  have hfzero (a : Fin k) (σ : 𝕊) (b : Fin k) (hb : b ∉ S) : f a σ b = 0 := by
    simp [f, hb]
  have hfedge (a : Fin k) (σ : 𝕊) (b : Fin k) (hb : b ∈ S) :
      f a σ b = ∑ t : Fin (m ⟨b, hb⟩),
        edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ := by
    simp only [f, dif_pos hb]
  refine ⟨S, V, hSne, hV, hbest, f, ?_, ?_⟩
  · constructor
    · exact fun a σ b hb => hfzero a σ b hb
    · intro i
      refine ⟨-G.L root i, ?_⟩
      intro b hb
      simp_rw [hfedge _ _ b hb]
      calc
        ∑ a : Fin k, ∑ t : Fin (m ⟨b, hb⟩),
            edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a (G.Φ a i) =
            ∑ t : Fin (m ⟨b, hb⟩), ∑ a : Fin k,
              edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a (G.Φ a i) :=
                Finset.sum_comm
        _ = ∑ t : Fin (m ⟨b, hb⟩),
              (G.L (path ⟨b, hb⟩ t.castSucc) i -
                G.L (path ⟨b, hb⟩ t.succ) i) := by
              apply Finset.sum_congr rfl
              intro t ht
              exact hedge _ _ (hpath ⟨b, hb⟩ t) i
        _ = G.L b i - G.L root i := by
              have htel := fin_sum_consecutive_sub_global
                (fun t : Fin (m ⟨b, hb⟩ + 1) => G.L (path ⟨b, hb⟩ t) i)
              simpa [hfirst ⟨b, hb⟩, hlast ⟨b, hb⟩] using htel
        _ = G.L b i + -G.L root i := by ring
  · intro a σ b
    by_cases hb : b ∈ S
    · rw [hfedge a σ b hb]
      calc
        |∑ t : Fin (m ⟨b, hb⟩),
            edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ| ≤
            ∑ t : Fin (m ⟨b, hb⟩),
              |edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t : Fin (m ⟨b, hb⟩), M := by
          apply Finset.sum_le_sum
          intro t ht
          dsimp [M]
          have h1 := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun x : Fin k => ∑ y : Fin k, ∑ c : Fin k, ∑ τ : 𝕊,
              |edge x y c τ|)
            (fun _ _ => Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ (path ⟨b, hb⟩ t.castSucc))
          have h2 := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun y : Fin k => ∑ c : Fin k, ∑ τ : 𝕊,
              |edge (path ⟨b, hb⟩ t.castSucc) y c τ|)
            (fun _ _ => Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ (path ⟨b, hb⟩ t.succ))
          have h3 := Finset.single_le_sum
              (s := Finset.univ)
              (f := fun c : Fin k => ∑ τ : 𝕊,
                |edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) c τ|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ a)
          have h4 := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun τ : 𝕊 =>
              |edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a τ|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
          exact h4.trans (h3.trans (h2.trans h1))
        _ = (m ⟨b, hb⟩ : ℝ) * M := by simp
        _ ≤ (k : ℝ) * M := mul_le_mul_of_nonneg_right
          (by exact_mod_cast hm ⟨b, hb⟩) hM
        _ = V := rfl
    · rw [hfzero a σ b hb]
      simpa using hV

end
end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hglo : BanditAlgorithm.GloballyObservable G) :
    ∃ S : Finset (Fin k), ∃ V : ℝ,
      S.Nonempty ∧ 0 ≤ V ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∃ f : Fin k → 𝕊 → Fin k → ℝ,
        BanditAlgorithm.PMVectorEstimatorOn G S f ∧ ∀ a σ b, |f a σ b| ≤ V :=
  BanditAlgorithm.globally_observable_bounded_vector_estimator G hk hd hglo
