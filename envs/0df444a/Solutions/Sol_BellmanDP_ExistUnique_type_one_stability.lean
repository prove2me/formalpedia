-- Prove2me | solution 1 for BellmanDP.ExistUnique.type_one_stability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:39:30.67851+00:00
-- url     : https://prove2.me/submissions/61b15c2f-2454-4bf6-927e-810c969a20e8

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes



namespace BellmanDP.ExistUnique

theorem lub_le_add_t1s {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, A q ≤ B q + K) :
    x ≤ y + K := by
  apply hx.2
  rintro _ ⟨q, rfl⟩
  have := hy.1 ⟨q, rfl⟩
  have := hK q
  linarith

theorem abs_lub_sub_t1s {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, |A q - B q| ≤ K) :
    |x - y| ≤ K := by
  have h1 := lub_le_add_t1s hx hy (fun q => by have := (abs_le.mp (hK q)).2; linarith)
  have h2 := lub_le_add_t1s hy hx (fun q => by have := (abs_le.mp (hK q)).1; linarith)
  rw [abs_le]; constructor <;> linarith

theorem rs_le_t1s {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (φ : EuclideanSpace ℝ (Fin N) → S → ℝ) (r M : ℝ)
    (hM : ∀ p ∈ D, ‖p‖ ≤ r → ∀ q, |φ p q| ≤ M) :
    ∀ p ∈ D, ‖p‖ ≤ r → ∀ q, |φ p q| ≤ radialSup D φ r := by
  intro p hp hpr q
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro x ⟨p', hp', hpc', q', rfl⟩
    exact hM p' hp' hpc' q'
  · exact ⟨p, hp, hpr, q, rfl⟩

theorem rs_nonneg_t1s {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (φ : EuclideanSpace ℝ (Fin N) → S → ℝ) (r : ℝ) : 0 ≤ radialSup D φ r := by
  apply Real.sSup_nonneg
  rintro x ⟨p', hp', hpc', q', rfl⟩
  exact abs_nonneg _

theorem t1s_core {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hg : TypeOne D g h T a) (hG : TypeOne D G h T a)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_cont : ContinuousWithinAt f D 0) (hf_zero : f 0 = 0)
    (hf : ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p)
    (hF_cont : ContinuousWithinAt F D 0) (hF_zero : F 0 = 0)
    (hF : ∀ p ∈ D, p ≠ 0 → SolvesAt G h T F p) (c : ℝ) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ ∑' n : ℕ, radialSup D (fun p q => G p q - g p q) (a ^ n * c) := by
  intro p0 hp0 hc0
  have hc : 0 ≤ c := le_trans (norm_nonneg _) hc0
  set u : ℝ → ℝ := fun r => radialSup D (fun p q => G p q - g p q) r with hu_def
  have hu : ∀ r, ∀ p ∈ D, ‖p‖ ≤ r → ∀ q, |G p q - g p q| ≤ u r := by
    intro r
    obtain ⟨Mg, hMg⟩ := hg.g_bdd r
    obtain ⟨MG, hMG⟩ := hG.g_bdd r
    apply rs_le_t1s D (fun p q => G p q - g p q) r (MG + Mg)
    intro p hp hpr q
    have := hMg p hp hpr q
    have := hMG p hp hpr q
    calc |G p q - g p q| ≤ |G p q| + |g p q| := abs_sub _ _
      _ ≤ MG + Mg := by linarith
  have hu0 : ∀ r, 0 ≤ u r := fun r => rs_nonneg_t1s D _ r
  have hule : ∀ r, u r ≤ radialSup D G r + radialSup D g r := by
    intro r
    obtain ⟨Mg, hMg⟩ := hg.g_bdd r
    obtain ⟨MG, hMG⟩ := hG.g_bdd r
    have hg' := rs_le_t1s D g r Mg hMg
    have hG' := rs_le_t1s D G r MG hMG
    have h0 := rs_nonneg_t1s D g r
    have h1 := rs_nonneg_t1s D G r
    apply Real.sSup_le _ (by linarith)
    rintro x ⟨p', hp', hpc', q', rfl⟩
    have := hg' p' hp' hpc' q'
    have := hG' p' hp' hpc' q'
    calc |G p' q' - g p' q'| ≤ |G p' q'| + |g p' q'| := abs_sub _ _
      _ ≤ _ := by linarith
  have hsum : Summable (fun n : ℕ => u (a ^ n * c)) := by
    apply Summable.of_nonneg_of_le (fun n => hu0 _) (fun n => hule _)
    exact (hG.summable_v c hc).add (hg.summable_v c hc)
  -- continuity of the difference
  have hd : ContinuousWithinAt (fun p => F p - f p) D 0 := hF_cont.sub hf_cont
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.mp hd ε hε
  have base : ∀ p ∈ D, ‖p‖ < δ → |F p - f p| ≤ ε := by
    intro p hp hpδ
    have := hδε hp (by simpa [dist_eq_norm] using hpδ)
    rw [Real.dist_eq, hF_zero, hf_zero] at this
    simp at this
    exact this.le
  have claim : ∀ n : ℕ, ∀ r : ℝ, ∀ p ∈ D, ‖p‖ ≤ r → a ^ n * r < δ →
      |F p - f p| ≤ (∑ j ∈ Finset.range n, u (a ^ j * r)) + ε := by
    intro n
    induction n with
    | zero =>
      intro r p hp hpr hr
      simp only [pow_zero, one_mul] at hr
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact base p hp (lt_of_le_of_lt hpr hr)
    | succ n ih =>
      intro r p hp hpr hr
      have hsnn : 0 ≤ ∑ j ∈ Finset.range (n + 1), u (a ^ j * r) :=
        Finset.sum_nonneg (fun j _ => hu0 _)
      by_cases hp0' : p = 0
      · subst hp0'; rw [hF_zero, hf_zero]; simp; linarith
      rw [Finset.sum_range_succ']
      have hsh : ∑ j ∈ Finset.range n, u (a ^ (j + 1) * r) = ∑ j ∈ Finset.range n, u (a ^ j * (a * r)) := by
        apply Finset.sum_congr rfl; intro j _; congr 1; ring
      rw [hsh]
      have : |F p - f p| ≤ u r + ((∑ j ∈ Finset.range n, u (a ^ j * (a * r))) + ε) := by
        apply abs_lub_sub_t1s (hF p hp hp0') (hf p hp hp0')
        intro q
        simp only [stageReturn]
        have hT := hg.T_le p hp q
        have hTr : ‖T p q‖ ≤ a * r := le_trans hT (mul_le_mul_of_nonneg_left hpr hg.a_nonneg)
        have h2 := ih (a * r) (T p q) (hg.mapsTo p hp q) hTr (by rw [← mul_assoc, ← pow_succ]; exact hr)
        have h1 := hu r p hp hpr q
        have h3 := hg.h_le_one p hp q
        have hnn : 0 ≤ (∑ j ∈ Finset.range n, u (a ^ j * (a * r))) + ε :=
          add_nonneg (Finset.sum_nonneg (fun j _ => hu0 _)) hε.le
        have h4 : |h p q * (F (T p q) - f (T p q))| ≤ (∑ j ∈ Finset.range n, u (a ^ j * (a * r))) + ε := by
          rw [abs_mul]
          calc |h p q| * |F (T p q) - f (T p q)| ≤ 1 * ((∑ j ∈ Finset.range n, u (a ^ j * (a * r))) + ε) :=
                mul_le_mul h3 h2 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        calc |G p q + h p q * F (T p q) - (g p q + h p q * f (T p q))|
            = |(G p q - g p q) + h p q * (F (T p q) - f (T p q))| := by ring_nf
          _ ≤ |G p q - g p q| + |h p q * (F (T p q) - f (T p q))| := abs_add_le _ _
          _ ≤ _ := by linarith
      simp only [pow_zero, one_mul] at this ⊢
      linarith
  have hlim : Filter.Tendsto (fun n : ℕ => a ^ n * c) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hg.a_nonneg hg.a_lt_one).mul_const c
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  have := claim n c p0 hp0 hc0 hn
  have hle : ∑ j ∈ Finset.range n, u (a ^ j * c) ≤ ∑' j, u (a ^ j * c) :=
    hsum.sum_le_tsum _ (fun j _ => hu0 _)
  linarith

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique


theorem solution {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hg : TypeOne D g h T a) (hG : TypeOne D G h T a)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_cont : ContinuousWithinAt f D 0) (hf_zero : f 0 = 0)
    (hf : ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p)
    (hF_cont : ContinuousWithinAt F D 0) (hF_zero : F 0 = 0)
    (hF : ∀ p ∈ D, p ≠ 0 → SolvesAt G h T F p) (c : ℝ) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ ∑' n : ℕ, radialSup D (fun p q => G p q - g p q) (a ^ n * c) := by
  exact t1s_core D g G h T a hg hG f F hf_cont hf_zero hf hF_cont hF_zero hF c
