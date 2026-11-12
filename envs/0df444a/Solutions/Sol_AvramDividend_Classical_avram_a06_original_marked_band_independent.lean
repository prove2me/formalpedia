-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_marked_band_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:18:59.785061+00:00
-- url     : https://prove2.me/submissions/39d4a5db-e3ad-409d-a43b-7ba31025d896

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_disjoint_count_increments_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_disjoint_iid_mark_sums_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_mark_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_levy_foundations_jumpCountLtIff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal
noncomputable section

/-- Original marked-band independence from count increments and IID marks. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      iIndepFun (fun (i : Fin n) ω =>
        ∑ j ∈ Finset.Ico
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ))
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ)),
        Y j ω) P := by
  classical
  intro n t ht
  let C : Fin (n + 1) → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
    fun i ω => LevyFoundations.jumpCount
      (fun k => LevyFoundations.arrival τ k ω) (t i : ℝ)
  let F : (Fin (n + 1) → ℕ) → Fin (n + 1) → ℕ :=
    fun v i => (Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i)).sup v
  let N : Fin (n + 1) → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
    fun i ω => F (fun j => C j ω) i
  have hCmeas : Measurable (fun ω => fun i => C i ω) := by
    refine measurable_pi_iff.2 ?_
    intro i
    exact AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
      τ hd.measurable_interarrival (t i : ℝ)
  have hFmeas : Measurable F := by
    unfold F
    fun_prop
  have hNmeas : Measurable (fun ω => fun i => N i ω) :=
    hFmeas.comp hCmeas
  have hNmono (ω) : Monotone (fun i => N i ω) := by
    intro i j hij
    dsimp [N, F]
    apply Finset.sup_le
    intro k hk
    exact Finset.le_sup (f := fun a : Fin (n + 1) => C a ω)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.trans hij⟩)
  have hCmono : ∀ᵐ ω ∂P, Monotone (fun i => C i ω) := by
    filter_upwards
      [levy_foundations_compoundDriverArrivalStrictMono hd (by norm_num),
       levy_foundations_compoundDriverArrivalDiverges hd (by norm_num)]
      with ω hstrict hdiv
    intro i j hij
    by_contra h
    have hlt : C j ω < C i ω := Nat.lt_of_not_ge h
    have htime := (levy_foundations_jumpCountLtIff
      (fun k => LevyFoundations.arrival τ k ω) hstrict hdiv
      (C j ω) (t i : ℝ)).mp hlt
    have hself : C j ω < C j ω :=
      (levy_foundations_jumpCountLtIff
        (fun k => LevyFoundations.arrival τ k ω) hstrict hdiv
        (C j ω) (t j : ℝ)).mpr (htime.trans (ht hij))
    exact (lt_irrefl _) hself
  have hCN : ∀ᵐ ω ∂P, ∀ i, N i ω = C i ω := by
    filter_upwards [hCmono] with ω hmono i
    apply le_antisymm
    · dsimp [N, F]
      apply Finset.sup_le
      intro j hj
      exact hmono (Finset.mem_filter.mp hj).2
    · dsimp [N, F]
      exact Finset.le_sup (f := fun a : Fin (n + 1) => C a ω)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)
  have hCountRaw :=
    AvramDividend.Classical.avram_a06_original_cp_disjoint_count_increments_independent
      P τ Y hd n t ht
  have hCount : iIndepFun (fun (i : Fin n) ω =>
      N i.succ ω - N i.castSucc ω) P := by
    apply ProbabilityTheory.iIndepFun.congr (fun i => ?_) hCountRaw
    filter_upwards [hCN] with ω h
    change C i.succ ω - C i.castSucc ω =
      N i.succ ω - N i.castSucc ω
    simp only [h]
  have hMarks : iIndepFun Y P := by
    have h := hd.indep.precomp (g := Sum.inr) Sum.inr_injective
    simpa [Function.comp] using h
  have hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P := by
    intro j k
    exact (hd.law_mark j).identDistrib (hd.law_mark k)
  have hYmeas : Measurable (fun ω => fun j => Y j ω) :=
    measurable_pi_iff.2 hd.measurable_mark
  have hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P := by
    have h := AvramDividend.Classical.avram_a06_original_cp_count_vector_mark_independent
      P τ Y hd (n + 1) t
    exact h.comp hFmeas measurable_id
  have hBlock :=
    AvramDividend.Classical.avram_a06_random_disjoint_iid_mark_sums_independent
      P n N Y hNmeas hYmeas hNmono hCount hMarks hSameLaw hSeparate
  apply ProbabilityTheory.iIndepFun.congr (fun i => ?_) hBlock
  filter_upwards [hCN] with ω h
  simp [N, C, h]
