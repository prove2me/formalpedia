-- Prove2me | solution 1 for DensInertW.diag_orth_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:12.26966+00:00
-- url     : https://prove2.me/submissions/af20cbc1-fcd0-4ff8-85c9-a1adbc6440c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_HermitianDiagonalization
import Theorems.Thm_DensInertW_Sub_finrank_perp_aniso
import Theorems.Thm_DensInertW_Sub_hfL_apply
import Theorems.Thm_DensInertW_Sub_hf_eq_zero_of_diag
import Theorems.Thm_DensInertW_Sub_hf_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]
namespace DensInertW
theorem _root_.solution {m q : ℕ} {B : Matrix (Fin m) (Fin m) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hB : IsHerm q B) (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0) :
    ∀ (d : ℕ) (W : Submodule L (Fin m → L)), finrank L W = d →
      ∃ (v : Fin d → Fin m → L) (r : ℕ), r ≤ d ∧ (∀ i, v i ∈ W) ∧ LinearIndependent L v ∧
        (∀ i j, i ≠ j → hf q B (v i) (v j) = 0) ∧ (∀ i, hf q B (v i) (v i) ≠ 0 ↔ i.val < r) := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hinv 0
    simp at h

  have iso : ∀ (d : ℕ) (W : Submodule L (Fin m → L)), finrank L W = d → (∀ e ∈ W, hf q B e e = 0) →
      ∃ (v : Fin d → Fin m → L) (r : ℕ), r ≤ d ∧ (∀ i, v i ∈ W) ∧ LinearIndependent L v ∧
        (∀ i j, i ≠ j → hf q B (v i) (v j) = 0) ∧ (∀ i, hf q B (v i) (v i) ≠ 0 ↔ i.val < r) := by
    intro d W hW h0
    have hz := hf_eq_zero_of_diag hadd hinv hB htr W h0
    let b := Module.finBasisOfFinrankEq L W hW
    refine ⟨fun i => (b i : Fin m → L), 0, Nat.zero_le _, fun i => (b i).2, ?_,
      fun i j _ => hz _ (b i).2 _ (b j).2, fun i => ?_⟩
    · exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    · simp [hz _ (b i).2 _ (b i).2]
  intro d
  induction d with
  | zero =>
    intro W hW
    by_cases h : ∃ e ∈ W, hf q B e e ≠ 0
    · obtain ⟨e, he, hee⟩ := h
      have := finrank_perp_aniso W e he hee
      omega
    · push_neg at h
      exact iso 0 W hW h
  | succ d ih =>
    intro W hW
    by_cases h : ∃ e ∈ W, hf q B e e ≠ 0
    · obtain ⟨e, he, hee⟩ := h
      have hd : finrank L ↥(W ⊓ LinearMap.ker (hfL q B e)) = d := by
        have := finrank_perp_aniso W e he hee
        omega
      obtain ⟨v, r, hr, hvW, hli, horth, hdiag⟩ := ih _ hd
      have hvk : ∀ i, hf q B (v i) e = 0 := fun i => by
        rw [← hfL_apply]
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp (hvW i)).2
      have hek : ∀ i, hf q B e (v i) = 0 := fun i => by
        rw [hf_symm hadd hinv hB, hvk i, zero_pow hq]
      refine ⟨Fin.cons e v, r + 1, by omega, fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_⟩
      · induction i using Fin.cases with
        | zero => simpa using he
        | succ j => simpa using (Submodule.mem_inf.mp (hvW j)).1
      · rw [linearIndependent_fin_cons]
        refine ⟨hli, fun hmem => hee ?_⟩
        have hle : Submodule.span L (Set.range v) ≤ LinearMap.ker (hfL q B e) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact (Submodule.mem_inf.mp (hvW i)).2
        have h1 := LinearMap.mem_ker.mp (hle hmem)
        rwa [hfL_apply] at h1
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hek j
        | succ i =>
          induction j using Fin.cases with
          | zero => simpa using hvk i
          | succ j => simpa using horth i j fun h => hij (by rw [h])
      · induction i using Fin.cases with
        | zero => simpa using hee
        | succ i =>
          simp only [Fin.cons_succ, Fin.val_succ]
          rw [hdiag i]
          omega
    · push_neg at h
      exact iso _ W hW h
end DensInertW
