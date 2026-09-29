-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fa0a6334-c743-5611-9589-ce35105b1ef5

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace ActRefl

open MvPowerSeries

section KerId
variable {R : Type} [CommRing R]

theorem mem_span_range_X_of_constantCoeff_eq_zero (f : MvPowerSeries (Fin 2) R) (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (Series.id R)) := by
  classical

  let g : MvPowerSeries (Fin 2) R := fun m => if m 1 = 0 then f m else 0
  have hg : ∀ m : Fin 2 →₀ ℕ, coeff m g = if m 1 = 0 then coeff m f else 0 := fun m => rfl
  have h1 : (X 1 : MvPowerSeries (Fin 2) R) ∣ f - g := by
    rw [X_dvd_iff]
    intro m hm
    rw [map_sub, hg, if_pos hm, sub_self]
  have h0 : (X 0 : MvPowerSeries (Fin 2) R) ∣ g := by
    rw [X_dvd_iff]
    intro m hm0
    rw [hg]
    split_ifs with hm1
    · have : m = 0 := by
        ext i
        fin_cases i
        · exact hm0
        · exact hm1
      rw [this, coeff_zero_eq_constantCoeff_apply, hf]
    · rfl
  have hX : ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) R) ∈ Ideal.span (Set.range (Series.id R)) :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨q₁, hq₁⟩ := h1
  obtain ⟨q₀, hq₀⟩ := h0
  have : f = X 1 * q₁ + X 0 * q₀ := by rw [← hq₁, ← hq₀]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hX 1)) (Ideal.mul_mem_right _ _ (hX 0))

noncomputable def ccAlgHom : MvPowerSeries (Fin 2) R →ₐ[R] R :=
  { (constantCoeff : MvPowerSeries (Fin 2) R →+* R) with
    commutes' := fun r => by
      show constantCoeff (algebraMap R (MvPowerSeries (Fin 2) R) r) = r
      rw [← c_eq_algebraMap]
      exact constantCoeff_C r }

theorem ccAlgHom_apply (f : MvPowerSeries (Fin 2) R) : ccAlgHom f = constantCoeff f := rfl

theorem ccAlgHom_surjective : Function.Surjective (ccAlgHom (R := R)) :=
  fun r => ⟨C r, constantCoeff_C r⟩

theorem ker_ccAlgHom_eq_span :
    RingHom.ker (ccAlgHom (R := R)) = Ideal.span (Set.range (Series.id R)) := by
  apply le_antisymm
  · intro f hf
    exact mem_span_range_X_of_constantCoeff_eq_zero f hf
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X i

noncomputable def kerAlgEquiv : (MvPowerSeries (Fin 2) R ⧸ Ideal.span (Set.range (Series.id R))) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R (ker_ccAlgHom_eq_span (R := R)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (ccAlgHom_surjective (R := R)))

end KerId

theorem hasKernelOfDegree_seriesId {B : Type} [CommRing B] :
    FormalODModule.HasKernelOfDegree (Series.id B) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Module.Finite.equiv (kerAlgEquiv (R := B)).symm.toLinearEquiv
  · exact Module.Projective.of_equiv (kerAlgEquiv (R := B)).symm.toLinearEquiv
  · intro κ _ f
    rw [Series.map_id, ← Module.finrank_self κ]
    exact LinearEquiv.finrank_eq (kerAlgEquiv (R := κ)).toLinearEquiv

theorem frobSeries_zero {p : ℕ} [Fact p.Prime] (B : Type) [CommRing B] :
    Rigidified.frobSeries (p := p) B 0 = Series.id B := by
  funext i
  show (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ 0) = MvPowerSeries.X i
  rw [pow_zero, pow_one]

end ActRefl

theorem solution
    (B : Type) [CommRing B] :
    FormalODModule.HasKernelOfDegree (Series.id B) 1 :=
  ActRefl.hasKernelOfDegree_seriesId

end S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id (solution)
