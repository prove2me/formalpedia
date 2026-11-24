-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_lidx_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:21.741586+00:00
-- url     : https://prove2.me/submissions/8ce3ab97-f9c3-4c88-9538-97b57b944deb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_locS_top
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_lidx_via
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (p : Ideal R) [p.IsPrime] {e f g : Fin d → Fin d → K}
    (he : LinearIndependent K e) (hf : LinearIndependent K f) (hg : LinearIndependent K g) :
    lidx p (Submodule.span R (Set.range e)) (Submodule.span R (Set.range g)) =
      lidx p (Submodule.span R (Set.range e)) (Submodule.span R (Set.range f)) +
        lidx p (Submodule.span R (Set.range f)) (Submodule.span R (Set.range g)) := by
  set A := Submodule.span R (Set.range e)
  set B := Submodule.span R (Set.range f)
  set C := Submodule.span R (Set.range g)
  have hfin : ∀ X Y : Submodule R (Fin d → K), X.FG → locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨c, hc, hcY⟩ :=
      indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hc hcY)
  have hAt : locS (nonZeroDivisors R) A = ⊤ := idxChange_locS_top he
  have hBt : locS (nonZeroDivisors R) B = ⊤ := idxChange_locS_top hf
  have hCt : locS (nonZeroDivisors R) C = ⊤ := idxChange_locS_top hg
  have hAfg : A.FG := Submodule.fg_span (Set.finite_range _)
  have hBfg : B.FG := Submodule.fg_span (Set.finite_range _)
  have hCfg : C.FG := Submodule.fg_span (Set.finite_range _)
  have hDt : locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
    rw [locBasic_locS_inf, locBasic_locS_inf, hAt, hBt, hCt]
    simp
  have hAD := hfin A _ hAfg hDt
  have hBD := hfin B _ hBfg hDt
  have hCD := hfin C _ hCfg hDt
  rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
      hAD hCD,
    indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
      hBD hCD]
  ring
end Formalism.DivisionValues
