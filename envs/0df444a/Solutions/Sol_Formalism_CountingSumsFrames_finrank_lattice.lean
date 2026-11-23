-- Prove2me | solution 1 for Formalism.CountingSumsFrames.finrank_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:25.672205+00:00
-- url     : https://prove2.me/submissions/f918f8a8-e1e2-428a-a356-2ca4fb60b736

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_intPol_torsionFree
import Theorems.Thm_Formalism_GM_TM_finrank_of_lattice_basis
import Theorems.Thm_Formalism_GM_TM_polZ_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} (LL : Letters N) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : S ≤ Pol p r LL) :
    Module.finrank ℤ_[p] (S.restrictScalars ℤ_[p] ⊓ PolZ p r LL : Submodule ℤ_[p] _) = Module.finrank ℚ_[p] S := by
  set L : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := S.restrictScalars ℤ_[p] ⊓ PolZ p r LL with hLdef
  have hLeq : L = S.restrictScalars ℤ_[p] ⊓ IntPol p (Fin N × Fin r) := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · intro x hx
      exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1,
        Submodule.mem_inf.mpr ⟨hS (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2⟩⟩
  have : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr (Submodule.FG.of_le (polZ_fg LL) inf_le_right)
  have := intPol_torsionFree L
  obtain ⟨k, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[p]) (M := L)
  have hk : Module.finrank ℤ_[p] L = k := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [hk]
  refine (finrank_of_lattice_basis S (fun i => (b i : MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)) ?_).symm
  rw [← hLeq]
  have : Set.range (fun i => (b i : MvPolynomial (Fin N × Fin r) ℚ_[p])) = L.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
end Formalism.CountingSumsFrames
