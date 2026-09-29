-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_one_self_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b255c65a-30f7-5a9f-b213-aff4bd8b72f8

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_one_self_of_isNoetherianRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

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
    {r : ℕ} [Fact r.Prime] (𝒪 : Type) [CommRing 𝒪]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : ModuliPackage.GPoint 𝒪 M B),
      ModuliPackage.G.IsActBy ι Φ η Fr E₀ 1 x x := by
  classical
  intro B _ _ _ x
  refine ⟨1, 0, 0, ?_, ?_, ?_, ?_⟩
  · rw [map_one, pow_zero, one_smul, inv_one, Units.val_one]
  · rw [mul_zero, pow_zero, OneMemClass.coe_one, MvFormalGroup.End.toPowerSeries_one]
    exact ActRefl.hasKernelOfDegree_seriesId
  · show x.ψ = x.ψ.comp _
    refine AlgHom.ext fun a => ?_
    simp
  · obtain ⟨n, f, hspan, hloc⟩ := hη.2.2 B (x.ψ : Onr →+* B) x.nilp x.pt
    refine ⟨n, f, hspan, ?_⟩
    intro i L _ _ _ hL
    haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) L inferInstance
    obtain ⟨t, ht, hηt⟩ := hloc i L hL
    refine ⟨t, t, ht, ht, hηt, hηt, rfl, 0, ?_⟩
    rw [add_zero, mul_zero, ActRefl.frobSeries_zero, Series.comp_id, OneMemClass.coe_one,
      MvFormalGroup.End.toPowerSeries_one]
    show _ = (t.Xbar.act _).comp (t.ρ.comp (((Series.id _).map (residueMap _)).comp (Series.id _)))
    rw [Series.map_id, Series.comp_id, Series.comp_id]

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_one_self_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_one_self_of_isNoetherianRing (solution)
