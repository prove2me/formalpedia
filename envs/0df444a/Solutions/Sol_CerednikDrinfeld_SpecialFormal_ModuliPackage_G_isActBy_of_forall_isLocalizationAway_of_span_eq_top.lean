-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_of_forall_isLocalizationAway_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/36e6c8c8-bf41-523b-9ebe-e477391c6477

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr) (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (x x' : ModuliPackage.GPoint 𝒪 M B)

    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hE : E₀ e = (r : K₀) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))

    (n : ℕ) (f : Fin n → B) (hspan : Ideal.span (Set.range f) = ⊤)

    (hleg : ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L],
      (algebraMap B L).comp (x'.ψ : Onr →+* B) = (algebraMap B L).comp ((frobTwist Onr Fr ((m' : ℤ) - 2 * k) x.ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (hloc : ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (r : L)),
      ∃ t t' : Rigidified r Φ L,
        t.IsAdmissible ι ((algebraMap B L).comp (x.ψ : Onr →+* B)) ∧ t'.IsAdmissible ι ((algebraMap B L).comp (x'.ψ : Onr →+* B)) ∧
        η L ((algebraMap B L).comp (x.ψ : Onr →+* B)) hL t =
          M.map (ψ' := (algebraMap B L).comp (x.ψ : Onr →+* B)) x.nilp hL (algebraMap B L) rfl x.pt ∧
        η L ((algebraMap B L).comp (x'.ψ : Onr →+* B)) hL t' =
          M.map (ψ' := (algebraMap B L).comp (x'.ψ : Onr →+* B)) x'.nilp hL (algebraMap B L) rfl x'.pt ∧
        Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries k m' ((algebraMap B L).comp (x.ψ : Onr →+* B)) t t') :
    ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' := by
  classical
  refine ⟨e, k, m', hE, hker, ?_, n, f, hspan, hloc⟩

  have hring : (x'.ψ : Onr →+* B) = ((frobTwist Onr Fr ((m' : ℤ) - 2 * k) x.ψ : Onr →ₐ[𝒪] B) : Onr →+* B) := by
    apply RingHom.ext
    intro y
    refine Module.eq_of_isLocalized_span (Set.range f) hspan (fun c : ↥(Set.range f) => Localization.Away c.1)
      (fun c : ↥(Set.range f) => Algebra.linearMap B (Localization.Away c.1)) _ _ ?_
    rintro ⟨_, i, rfl⟩
    exact congrFun (congrArg DFunLike.coe (hleg i (Localization.Away (f i)))) y
  exact AlgHom.coe_ringHom_injective hring

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top (solution)
