-- Prove2me | solution 1 for FormalGroup.exists_lawHom_series_eq_variableChangeSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8c43bc1a-b61a-51ce-ae22-4a2c64197568

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_lawHom_series_eq_variableChangeSeries
p2m_attr_erase "instance" "WeierstrassCurve.instIsCommFormalGroup"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem solution
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
    (F₁ F₂ : FormalGroup R) (h₁ : F₁.toPowerSeries = W.formalGroupLawFixed)
    (h₂ : F₂.toPowerSeries = (C • W).formalGroupLawFixed) :
    ∃ σ : FormalGroup.LawHom F₁ F₂, σ.series = W.variableChangeSeries C := by
  refine ⟨{ series := W.variableChangeSeries C
            constantCoeff_series := W.constantCoeff_variableChangeSeries C
            comm := ?_ }, rfl⟩
  rw [h₁, h₂]
  exact (W.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed C).2

end S_FormalGroup_exists_lawHom_series_eq_variableChangeSeries
end P2MW
export P2MW.S_FormalGroup_exists_lawHom_series_eq_variableChangeSeries (solution)
