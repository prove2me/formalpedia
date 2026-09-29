-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_of_isTranslate_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f01f9a33-4352-5d9f-885e-0c6d47b43ad2

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_isTranslate_of_hasKernelOfDegree

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

namespace T2CORE

open MvPowerSeries (constantCoeff)

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
  {B : Type} [CommRing B] {L : Type} [CommRing L]

theorem frobSeries_cc (B : Type) [CommRing B] (j : ℕ) : ∀ i, constantCoeff (Rigidified.frobSeries (p := p) B j i) = 0 := by
  intro i
  show constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ j)) = 0
  rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

theorem frobSeries_map (f : B →+* L) (j : ℕ) :
    (Rigidified.frobSeries (p := p) B j).map f = Rigidified.frobSeries (p := p) L j := by
  funext i
  show MvPowerSeries.map f ((MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ j)) = _
  rw [map_pow, MvPowerSeries.map_X]
  rfl

omit [Fact p.Prime] in
theorem mk_comp_eq (φ : B →+* L) :
    (Ideal.Quotient.mk (pIdeal p L)).comp φ = (reduceMap (p := p) φ).comp (Ideal.Quotient.mk (pIdeal p B)) :=
  RingHom.ext fun _ => rfl

theorem Xbar_map (φ : B →+* L) (t : Rigidified p Φ B) :
    (t.map φ).Xbar = t.Xbar.map (reduceMap φ) := by
  show (t.X.map φ).map (Ideal.Quotient.mk (pIdeal p L)) = (t.X.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap φ)
  rw [FormalODModule.map_map, FormalODModule.map_map, mk_comp_eq]

theorem isTranslate_map (φ : B →+* L) (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) (ψ : O →+* B)
    (t t' : Rigidified p Φ B) (he : ∀ i, constantCoeff (e i) = 0)
    (hρ : ∀ i, constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0)
    (h : Rigidified.IsTranslate e k m' ψ t t') :
    Rigidified.IsTranslate e k m' (φ.comp ψ) (t.map φ) (t'.map φ) := by
  obtain ⟨hX, c, hc⟩ := h
  refine ⟨by rw [Rigidified.map_X, Rigidified.map_X, hX], c, ?_⟩
  set f := reduceMap (p := p) φ with hf
  have key := congrArg (Series.map f) hc

  have cF : ∀ j i, constantCoeff (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j i) = 0 := frobSeries_cc _
  have ce : ∀ i, constantCoeff ((Series.map (residueMap ψ) e) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map _ (e i)) = 0
    rw [MvPowerSeries.constantCoeff_map, he i, map_zero]
  rw [Series.map_comp f _ _ (Series.constantCoeff_comp hρ' (cF m')), Series.map_comp f _ _ (cF m'),
    Series.map_comp f _ _ (Series.constantCoeff_comp hρ (Series.constantCoeff_comp ce (cF (2 * k)))),
    Series.map_comp f _ _ (Series.constantCoeff_comp ce (cF (2 * k))), Series.map_comp f _ _ (cF (2 * k)),
    frobSeries_map, frobSeries_map, Series.map_map, ← residueMap_comp,
    ← FormalODModule.map_act, ← FormalODModule.map_act] at key
  rw [Xbar_map, Rigidified.map_ρ, Rigidified.map_ρ, Rigidified.map_n, Rigidified.map_n]
  exact key

end T2CORE

open T2CORE in
theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr) (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)

    (hηnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
      η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hBr : IsNilpotent (r : B))
    (χ χ' : Onr →ₐ[𝒪] B) (t t' : Rigidified r Φ B)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hleg : χ' = frobTwist Onr Fr ((m' : ℤ) - 2 * k) χ)
    (ht : t.IsAdmissible ι (χ : Onr →+* B)) (ht' : t'.IsAdmissible ι (χ' : Onr →+* B))
    (hE : E₀ e = (r : K₀) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries k m' (χ : Onr →+* B) t t') :
    ModuliPackage.G.IsActBy ι Φ η Fr E₀ g
      (⟨χ, hBr, η B (χ : Onr →+* B) hBr t⟩ : ModuliPackage.GPoint 𝒪 M B) ⟨χ', hBr, η B (χ' : Onr →+* B) hBr t'⟩  := by
  classical
  refine ⟨e, k, m', hE, hker, hleg, 1, fun _ => (1 : B), ?_, ?_⟩
  · rw [show Set.range (fun _ : Fin 1 => (1 : B)) = {1} from Set.range_const, Ideal.span_singleton_one]
  · intro i L _ _ _ hL
    haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers ((fun _ : Fin 1 => (1 : B)) i)) L inferInstance
    refine ⟨t.map (algebraMap B L), t'.map (algebraMap B L),
      Rigidified.IsAdmissible.map_ringHom ι (χ : Onr →+* B) (algebraMap B L) t ht,
      Rigidified.IsAdmissible.map_ringHom ι (χ' : Onr →+* B) (algebraMap B L) t' ht',
      hηnat B L (χ : Onr →+* B) _ hBr hL (algebraMap B L) rfl t ht,
      hηnat B L (χ' : Onr →+* B) _ hBr hL (algebraMap B L) rfl t' ht', ?_⟩
    exact isTranslate_map (algebraMap B L) _ k m' (χ : Onr →+* B) t t'
      (e : MvFormalGroup.End Φ.F).constantCoeff_eq_zero ht.constantCoeff_ρ ht'.constantCoeff_ρ htr

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_isTranslate_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_isTranslate_of_hasKernelOfDegree (solution)
