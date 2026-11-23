-- Prove2me | solution 1 for DensInertW.anisoPeel_of_valCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:21.557696+00:00
-- url     : https://prove2.me/submissions/edae64fe-de0d-4c0f-a865-a05de667f9e9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel
import Theorems.Thm_DensInertW_an_cntT_eq
import Theorems.Thm_DensInertW_an_fiber
import Theorems.Thm_DensInertW_Sub_finrank_perp_aniso
import Theorems.Thm_DensInertW_Sub_nondeg_perp_aniso
import Theorems.Thm_DensInertW_frob_add
import Theorems.Thm_DensInertW_frob_frob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
open DensInertW.Sub
namespace DensInertW
theorem _root_.solution (hv : ValCount) : AnisoPeel := by
  intro K L _ _ _ _ _ h2 n M W hM hW m b w k hbf hb0 hk
  classical
  have hadd : ∀ a b : L, (a + b) ^ Fintype.card K = a ^ Fintype.card K + b ^ Fintype.card K :=
    fun a b => frob_add (K := K) a b
  have hinv : ∀ a : L, (a ^ Fintype.card K) ^ Fintype.card K = a := frob_frob h2
  rw [an_cntT_eq]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun X : Fin (m + 1) → Fin n → L => X 0)
    (t := Finset.univ.filter (fun x : Fin n → L => x ∈ W ∧ hf (Fintype.card K) M x x = b))]
  · push_cast
    have hterm : ∀ x ∈ Finset.univ.filter (fun x : Fin n → L =>
        x ∈ W ∧ hf (Fintype.card K) M x x = b),
        (((Finset.univ.filter (anP (Fintype.card K) M W
          (Matrix.diagonal (Fin.cons b w : Fin (m + 1) → L)))).filter
          (fun X : Fin (m + 1) → Fin n → L => X 0 = x)).card : ℤ) = k := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hxW, hxx⟩ := hx
      have hee : hf (Fintype.card K) M x x ≠ 0 := hxx ▸ hb0
      rw [Finset.filter_filter, an_fiber hadd hinv hM W b w x hxW hxx hb0]
      have hk' := hk _ (nondeg_perp_aniso hadd W hW x hxW hee) (finrank_perp_aniso W x hxW hee)
      rw [an_cntT_eq] at hk'
      exact hk'
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (fun x : Fin n → L =>
        x ∈ W ∧ hf (Fintype.card K) M x x = b)).card : ℤ) =
        valN (Fintype.card K) (Module.finrank L W) := by
      have h0 := hv K L h2 n M W hM hW b hbf
      rw [if_neg hb0] at h0
      rw [← h0, ← Set.ncard_coe_finset]
      congr 2
      ext v
      simp
    rw [hcard]
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hX'.1 0, ?_⟩
    rw [hX'.2.2 0 0, Matrix.diagonal_apply_eq, Fin.cons_zero]
end DensInertW
