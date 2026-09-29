-- Prove2me | solution 1 for CuspForm.HeckeGaloisRepDatum.exists_pi_eq_and_isFlatAt_of_comp_pi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/eb25384b-9aff-5416-a530-1197a7c32a08

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import Theorems.Thm_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_rho_eq_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_isFlatAt_of_comp_pi_eq
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

open Polynomial

namespace CuspForm p2m_export "CuspForm" "HeckeGaloisRepDatum heckeAlgebra HeckeGaloisRepDatum.exists_pi_eq_and_rho_eq_baseChangeAlong" namespace HeckeGaloisRepDatum p2m_export "CuspForm.HeckeGaloisRepDatum" "ρ π residue_surjective exists_pi_eq_and_rho_eq_baseChangeAlong" end CuspForm.HeckeGaloisRepDatum
namespace CuspForm.HeckeGaloisRepDatum
p2m_open_scoped "CuspForm CuspForm.HeckeGaloisRepDatum" in

private theorem _root_.CuspForm.HeckeGaloisRepDatum.finite_residueField
    {N : ℕ} [NeZero N] {S : Set ℕ}
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪}
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) :
    Finite (IsLocalRing.ResidueField T) := by
  refine Finite.of_surjective (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)) ?_
  intro y
  obtain ⟨x, hx⟩ := H.residue_surjective y
  exact ⟨IsLocalRing.residue 𝒪 x, by rw [IsLocalRing.ResidueField.map_residue]; exact hx⟩

end CuspForm.HeckeGaloisRepDatum
p2m_export "" "CuspForm.HeckeGaloisRepDatum.finite_residueField"

theorem solution
    {N : ℕ} [NeZero N] {S : Finset ℕ}
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T₀ : Type} [CommRing T₀] [IsLocalRing T₀] [IsNoetherianRing T₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal T₀) T₀] [Algebra 𝒪 T₀]
    [IsLocalHom (algebraMap 𝒪 T₀)] [Module.Finite 𝒪 T₀] [Module.Free 𝒪 T₀]
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
    [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H₀ : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T₀)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T)
    (φ : T₀ →ₐ[𝒪] T) (hφ : IsLocalHom φ.toRingHom) (hfac : ∀ t, φ (H₀.π t) = H.π t)
    {p : ℕ} (hflat : H₀.ρ.IsFlatAt p) :
    ∃ H' : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T, H'.π = H.π ∧ H'.ρ.IsFlatAt p := by
  haveI : Finite (IsLocalRing.ResidueField T₀) := hflat.1
  haveI : Finite (IsLocalRing.ResidueField 𝒪) :=
    Finite.of_injective (IsLocalRing.ResidueField.map (algebraMap 𝒪 T₀))
      (IsLocalRing.ResidueField.map (algebraMap 𝒪 T₀)).injective
  obtain ⟨H', hπ, hρ⟩ :=
    CuspForm.HeckeGaloisRepDatum.exists_pi_eq_and_rho_eq_baseChangeAlong H₀ H φ hφ hfac
  refine ⟨H', hπ, ?_⟩
  rw [hρ]
  haveI : Finite (IsLocalRing.ResidueField T) := H.finite_residueField
  exact GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField φ.toRingHom hφ H₀.ρ hflat

end S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_isFlatAt_of_comp_pi_eq
end P2MW
export P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_isFlatAt_of_comp_pi_eq (solution)
