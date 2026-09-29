-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.localizedModule_mk_eq_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a948619b-ea0e-5bf9-a89f-582dad8ed1bf

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

namespace K73SC

theorem awayToLoc_mul_eq {B : Type} [CommRing B] (x : PrimeSpectrum B) (g : B) (hg : g ∉ x.asIdeal)
    (w : Rigidified.Baway g) (a d : B) (hw : w * Rigidified.awayHom g d = Rigidified.awayHom g a) :
    Rigidified.awayToLoc x g hg w * Rigidified.locHom x d = Rigidified.locHom x a := by
  have h1 : Rigidified.awayToLoc x g hg (Rigidified.awayHom g d) = Rigidified.locHom x d :=
    IsLocalization.Away.lift_eq g _ d
  have h2 : Rigidified.awayToLoc x g hg (Rigidified.awayHom g a) = Rigidified.locHom x a :=
    IsLocalization.Away.lift_eq g _ a
  rw [← h1, ← map_mul, hw, h2]

end K73SC

theorem solution
    {p : ℕ} [Fact p.Prime]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B'] (f : B →ₐ[ℤ_[p]] B')
    (N : Submodule B (Fin 2 → B)) (N' : Submodule B' (Fin 2 → B'))
    (T : Type) [AddCommGroup T] [Module B T] (T' : Type) [AddCommGroup T'] [Module B' T']
    (σ : T ≃ₗ[B] ↥N) (σ' : T' ≃ₗ[B'] ↥N')
    (τ : T →ₛₗ[(f : B →+* B')] T')
    (hτσ : ∀ (r : T) (i : Fin 2), ((σ' (τ r) : ↥N') : Fin 2 → B') i = f (((σ r : ↥N) : Fin 2 → B) i))
    (x' : PrimeSpectrum B') (g : B) (hg : g ∉ (PrimeSpectrum.comap (f : B →+* B') x').asIdeal)
    (hg' : f g ∉ x'.asIdeal)
    (fg : Rigidified.Baway g →+* Rigidified.Baway (f g))
    (hfg : fg.comp (Rigidified.awayHom g) = (Rigidified.awayHom (f g)).comp (f : B →+* B'))
    (tt sQ : T) (s : B) (hs : f s ∉ x'.asIdeal) (b : (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl)
    (heq : LocalizedModule.mk tt
        (⟨s, fun h => hs (by simpa using (Ideal.mem_comap.mp h))⟩ : (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl) =
      LocalizedModule.mk sQ b)
    (w : Fin 2 → Rigidified.Baway g)
    (hσb : ∀ i, Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') (((σ sQ : ↥N) : Fin 2 → B) i) =
      Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') (b : B) *
        Rigidified.awayToLoc (PrimeSpectrum.comap (f : B →+* B') x') g hg (w i))
    (s' : T') (b' : x'.asIdeal.primeCompl) (w' : Fin 2 → Rigidified.Baway (f g))
    (hσb' : ∀ i, Rigidified.locHom x' (((σ' s' : ↥N') : Fin 2 → B') i) =
      Rigidified.locHom x' (b' : B') * Rigidified.awayToLoc x' (f g) hg' (w' i))
    (hw : ∀ i, w' i = fg (w i)) :
    LocalizedModule.mk s' b' = LocalizedModule.mk (τ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl) := by
  classical

  obtain ⟨u₁, hu₁⟩ := LocalizedModule.mk_eq.mp heq
  have hxmem : ∀ z : B, z ∈ (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl → f z ∈ x'.asIdeal.primeCompl :=
    fun z hz hz' => hz (Ideal.mem_comap.mpr hz')

  suffices H : ∀ i : Fin 2, ∃ U : x'.asIdeal.primeCompl,
      (U : B') * (f s * ((σ' s' : ↥N') : Fin 2 → B') i) = (U : B') * ((b' : B') * f (((σ tt : ↥N) : Fin 2 → B) i)) by
    obtain ⟨U0, hU0⟩ := H 0
    obtain ⟨U1, hU1⟩ := H 1
    rw [LocalizedModule.mk_eq]
    refine ⟨U0 * U1, ?_⟩
    apply σ'.injective
    apply Subtype.ext
    funext i
    simp only [Submonoid.smul_def, Submonoid.coe_mul, map_smul, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, hτσ]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · linear_combination ((U1 : B')) * hU0
    · linear_combination ((U0 : B')) * hU1
  intro i

  obtain ⟨⟨a, ⟨d, hd⟩⟩, hwa⟩ := IsLocalization.surj (Submonoid.powers g) (w i)
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hd
  have hwa0 : w i * Rigidified.awayHom g (g ^ n) = Rigidified.awayHom g a := hwa
  have h2 : Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') ((((σ sQ : ↥N) : Fin 2 → B) i) * g ^ n) =
      Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') ((b : B) * a) := by
    rw [map_mul, hσb i, mul_assoc, K73SC.awayToLoc_mul_eq _ g hg (w i) a (g ^ n) hwa0, map_mul]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl (Rigidified.Bloc (PrimeSpectrum.comap (f : B →+* B') x'))).mp h2

  have hfg' : ∀ z : B, fg (Rigidified.awayHom g z) = Rigidified.awayHom (f g) (f z) := fun z =>
    congrArg (fun φ : B →+* Rigidified.Baway (f g) => φ z) hfg
  have hwa' : w' i * Rigidified.awayHom (f g) (f (g ^ n)) = Rigidified.awayHom (f g) (f a) := by
    rw [hw i, ← hfg', ← hfg', ← map_mul, hwa0]
  have h3 : Rigidified.locHom x' ((((σ' s' : ↥N') : Fin 2 → B') i) * f (g ^ n)) = Rigidified.locHom x' ((b' : B') * f a) := by
    rw [map_mul, hσb' i, mul_assoc, K73SC.awayToLoc_mul_eq x' (f g) hg' (w' i) (f a) (f (g ^ n)) hwa', map_mul]
  obtain ⟨c', hc'⟩ := (IsLocalization.eq_iff_exists x'.asIdeal.primeCompl (Rigidified.Bloc x')).mp h3
  rw [map_pow] at hc'

  have h1 : f (u₁ : B) * f (b : B) * f (((σ tt : ↥N) : Fin 2 → B) i) = f (u₁ : B) * f s * f (((σ sQ : ↥N) : Fin 2 → B) i) := by
    have := congrArg (fun r : T => f (((σ r : ↥N) : Fin 2 → B) i)) hu₁
    simp only [Submonoid.smul_def, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul] at this
    linear_combination this
  have h2f : f (c : B) * (f (((σ sQ : ↥N) : Fin 2 → B) i) * f g ^ n) = f (c : B) * (f (b : B) * f a) := by
    have := congrArg f hc
    simp only [map_mul, map_pow] at this
    exact this

  have hU : (c' : B') * f (c : B) * f (u₁ : B) * f (b : B) * f g ^ n ∈ x'.asIdeal.primeCompl :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ c'.2 (hxmem _ c.2))
      (hxmem _ u₁.2)) (hxmem _ b.2)) (Submonoid.pow_mem _ hg' n)
  refine ⟨⟨(c' : B') * f (c : B) * f (u₁ : B) * f (b : B) * f g ^ n, hU⟩, ?_⟩
  simp only
  linear_combination (f (c : B) * f (u₁ : B) * f (b : B) * f s) * hc' + ((c' : B') * (b' : B') * f (u₁ : B) * f s) * h2f.symm +
    ((c' : B') * (b' : B') * f (c : B) * f g ^ n) * h1.symm

end S_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord (solution)
