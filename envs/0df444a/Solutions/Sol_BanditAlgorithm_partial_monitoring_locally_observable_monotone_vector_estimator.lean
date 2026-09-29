-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_locally_observable_monotone_vector_estimator
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T18:25:29.69122+00:00
-- url     : https://prove2.me/submissions/c11392bd-0ddd-40be-a3f7-34dba66a4938

import Theorems.Thm_BanditAlgorithm_partial_monitoring_pareto_monotone_neighbour_paths
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_loss_interpolation
import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

private lemma fin_sum_consecutive_sub {n : ℕ} (g : Fin (n + 1) → ℝ) :
    ∑ t : Fin n, (g t.castSucc - g t.succ) = g 0 - g (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun t : Fin (n + 1) ↦ g t.succ)
      have htail' : ∑ i : Fin n, (g i.succ.castSucc - g i.succ.succ) =
          g (Fin.succ 0) - g (Fin.last n).succ := by
        calc
          ∑ i : Fin n, (g i.succ.castSucc - g i.succ.succ) =
              ∑ i : Fin n, (g i.castSucc.succ - g i.succ.succ) := by
                apply Finset.sum_congr rfl
                intro i hi
                congr 2
          _ = g (Fin.succ 0) - g (Fin.last n).succ := htail
      rw [htail']
      have hz : g (Fin.castSucc 0) = g 0 := by
        apply congrArg g
        apply Fin.ext
        rfl
      have hl : g (Fin.last n).succ = g (Fin.last (n + 1)) := by
        apply congrArg g
        apply Fin.ext
        rfl
      rw [hz, hl]
      ring

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ V : ℝ,
      S.Nonempty ∧ 0 ≤ V ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
        ∃ f : Fin k → 𝕊 → Fin k → ℝ,
          PMVectorEstimatorOn G S f ∧
          (∀ a σ b, |f a σ b| ≤ V) ∧
          ∀ a σ b, f a σ b ≠ 0 →
            ∑ i : Fin d, G.L a i * lam i ≤
              ∑ i : Fin d, G.L b i * lam i := by
  classical
  obtain ⟨S, hS, hbest, hpaths⟩ :=
    partial_monitoring_pareto_monotone_neighbour_paths G hk hd
  let edge : Fin k → Fin k → Fin k → 𝕊 → ℝ := fun x y ↦
    if h : NeighbouringActions G x y then
      fun a σ ↦ Classical.choose (hloc x y h) (a, σ)
    else 0
  have hedge (x y : Fin k) (hxy : NeighbouringActions G x y) :
      IsLocalLossEstimator G x y (fun z ↦ edge x y z.1 z.2) := by
    dsimp [edge]
    rw [dif_pos hxy]
    exact Classical.choose_spec (hloc x y hxy)
  let M : ℝ := ∑ x : Fin k, ∑ y : Fin k, ∑ a : Fin k, ∑ σ : 𝕊,
    |edge x y a σ|
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  let V : ℝ := (k : ℝ) * M
  have hV : 0 ≤ V := mul_nonneg (by exact_mod_cast (Nat.zero_le k)) hM
  refine ⟨S, V, hS, hV, hbest, ?_⟩
  intro lam hlam
  obtain ⟨root, hroot, hrootpaths⟩ := hpaths lam hlam
  let B := {b : Fin k // b ∈ S}
  have hrootpaths' : ∀ b : B,
      ∃ m : ℕ, ∃ path : Fin (m + 1) → Fin k,
        m ≤ k ∧ path 0 = b.1 ∧ path (Fin.last m) = root ∧
        (∀ t, path t ∈ S) ∧
        ∀ t : Fin m,
          NeighbouringActions G (path t.castSucc) (path t.succ) ∧
          ∑ i : Fin d, G.L (path t.succ) i * lam i ≤
            ∑ i : Fin d, G.L (path t.castSucc) i * lam i :=
    fun b ↦ hrootpaths b.1 b.2
  choose m path hm hfirst hlast hpathS hpath using hrootpaths'
  let f : Fin k → 𝕊 → Fin k → ℝ := fun a σ b ↦
    if hb : b ∈ S then ∑ t : Fin (m ⟨b, hb⟩),
      edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ else 0
  have hfzero (a : Fin k) (σ : 𝕊) (b : Fin k) (hb : b ∉ S) : f a σ b = 0 := by
    simp [f, hb]
  have hfedge (a : Fin k) (σ : 𝕊) (b : Fin k) (hb : b ∈ S) :
      f a σ b = ∑ t : Fin (m ⟨b, hb⟩),
        edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ := by
    simp only [f, dif_pos hb]
  refine ⟨f, ?_, ?_, ?_⟩
  · constructor
    · exact fun a σ b hb ↦ hfzero a σ b hb
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
        _ =
            ∑ t : Fin (m ⟨b, hb⟩),
              (G.L (path ⟨b, hb⟩ t.castSucc) i - G.L (path ⟨b, hb⟩ t.succ) i) := by
              apply Finset.sum_congr rfl
              intro t ht
              exact (hedge _ _ (hpath ⟨b, hb⟩ t).1).1 i
        _ = G.L b i - G.L root i := by
          have htel : ∑ t : Fin (m ⟨b, hb⟩),
              (G.L (path ⟨b, hb⟩ t.castSucc) i - G.L (path ⟨b, hb⟩ t.succ) i) =
              G.L (path ⟨b, hb⟩ 0) i -
                G.L (path ⟨b, hb⟩ (Fin.last (m ⟨b, hb⟩))) i := by
            exact fin_sum_consecutive_sub
              (fun t : Fin (m ⟨b, hb⟩ + 1) ↦ G.L (path ⟨b, hb⟩ t) i)
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
            (f := fun x : Fin k ↦ ∑ y : Fin k, ∑ c : Fin k, ∑ τ : 𝕊, |edge x y c τ|)
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
              Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ (path ⟨b, hb⟩ t.castSucc))
          have h2 := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun y : Fin k ↦ ∑ c : Fin k, ∑ τ : 𝕊,
              |edge (path ⟨b, hb⟩ t.castSucc) y c τ|)
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
              Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ (path ⟨b, hb⟩ t.succ))
          have h3 := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun c : Fin k ↦ ∑ τ : 𝕊,
              |edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) c τ|)
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ a)
          have h4 := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun τ : 𝕊 ↦
              |edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a τ|)
            (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ σ)
          exact h4.trans (h3.trans (h2.trans h1))
        _ = (m ⟨b, hb⟩ : ℝ) * M := by simp
        _ ≤ (k : ℝ) * M :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hm ⟨b, hb⟩) hM
        _ = V := rfl
    · simp [hfzero a σ b hb, hV]
  · intro a σ b hfab
    have hb : b ∈ S := by
      by_contra hb
      exact hfab (hfzero a σ b hb)
    rw [hfedge a σ b hb] at hfab
    have hex : ∃ t : Fin (m ⟨b, hb⟩),
        edge (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) a σ ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      exact hfab (Finset.sum_eq_zero fun t _ ↦ hnone t)
    obtain ⟨t, ht⟩ := hex
    have hlocal := (hedge _ _ (hpath ⟨b, hb⟩ t).1).2 a
    have haN : a ∈ pmNeighbourhood G
        (path ⟨b, hb⟩ t.castSucc) (path ⟨b, hb⟩ t.succ) := by
      by_contra ha
      exact ht (hlocal ha σ)
    obtain ⟨α, hα0, hα1, hinterp⟩ :=
      partial_monitoring_neighbour_loss_interpolation G _ _ (hpath ⟨b, hb⟩ t).1 a haN
    have hinterpLoss :
        ∑ i : Fin d, G.L a i * lam i =
          α * (∑ i : Fin d, G.L (path ⟨b, hb⟩ t.castSucc) i * lam i) +
            (1 - α) * (∑ i : Fin d, G.L (path ⟨b, hb⟩ t.succ) i * lam i) := by
      calc
        ∑ i : Fin d, G.L a i * lam i =
            ∑ i : Fin d,
              (α * G.L (path ⟨b, hb⟩ t.castSucc) i +
                (1 - α) * G.L (path ⟨b, hb⟩ t.succ) i) * lam i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hinterp i]
        _ = α * (∑ i : Fin d, G.L (path ⟨b, hb⟩ t.castSucc) i * lam i) +
            (1 - α) * (∑ i : Fin d, G.L (path ⟨b, hb⟩ t.succ) i * lam i) := by
              simp only [add_mul, Finset.sum_add_distrib]
              congr 1
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
    have hstep := (hpath ⟨b, hb⟩ t).2
    have hle_child :
        ∑ i : Fin d, G.L a i * lam i ≤
          ∑ i : Fin d, G.L (path ⟨b, hb⟩ t.castSucc) i * lam i := by
      rw [hinterpLoss]
      nlinarith
    have hpathmono : ∀ j : Fin (m ⟨b, hb⟩ + 1),
        ∑ i : Fin d, G.L (path ⟨b, hb⟩ j) i * lam i ≤
          ∑ i : Fin d, G.L b i * lam i := by
      intro j
      have hprefix : ∀ n : ℕ, ∀ hn : n ≤ m ⟨b, hb⟩,
          ∑ i : Fin d, G.L (path ⟨b, hb⟩ ⟨n, Nat.lt_succ_of_le hn⟩) i * lam i ≤
            ∑ i : Fin d, G.L b i * lam i := by
        intro n hn
        induction n with
        | zero => simp [hfirst ⟨b, hb⟩]
        | succ n ih =>
            have hnlt : n < m ⟨b, hb⟩ := Nat.lt_of_succ_le hn
            exact (hpath ⟨b, hb⟩ ⟨n, hnlt⟩).2.trans (ih (Nat.le_of_lt hnlt))
      exact hprefix j j.is_le
    exact hle_child.trans (hpathmono t.castSucc)

end
end BanditAlgorithm
