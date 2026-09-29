-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.PeriodDatum.comp_pullback_mem_periodLattice_of_forall_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/643df89d-2fef-5209-b84f-bcc7c270fd3f

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_comp_pullback_mem_periodLattice_of_forall_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve

theorem solution
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq E₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq E₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂} (μ : D₁.FiniteHom D₂)
    {K₁ K₂ L : Type} [Field K₁] [Field K₂] [Field L] [Algebra K₁ L] [Algebra K₂ L]
    {ord₁ : Additive K₁ˣ →+ ℤ} {ord₂ : Additive K₂ˣ →+ ℤ}
    (P₁ : PeriodDatum D₁ K₁ L ord₁) (P₂ : PeriodDatum D₂ K₂ L ord₂)
    (hproj : ∀ (x : ↥(ribbonKernel D₂)) (y : ↥(ribbonKernel D₁)),
      algebraMap K₁ L (((Additive.toMul (P₁.Q (μ.pullback x) y)) : K₁ˣ) : K₁) =
        algebraMap K₂ L (((Additive.toMul (P₂.Q x (μ.pushforward y))) : K₂ˣ) : K₂))
    (u' : P₁.TorusPoints) (hu' : u' ∈ P₁.periodLattice) :
    u'.comp μ.pullback ∈ P₂.periodLattice := by
  obtain ⟨y₀, rfl⟩ := hu'
  refine ⟨μ.pushforward y₀, ?_⟩
  ext x
  rw [LinearMap.comp_apply, PeriodDatum.QL_apply, PeriodDatum.QL_apply, P₁.Q_symm, P₂.Q_symm]
  exact (hproj x y₀).symm

end S_CerednikDrinfeld_Mumford_PeriodDatum_comp_pullback_mem_periodLattice_of_forall_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_comp_pullback_mem_periodLattice_of_forall_eq (solution)
