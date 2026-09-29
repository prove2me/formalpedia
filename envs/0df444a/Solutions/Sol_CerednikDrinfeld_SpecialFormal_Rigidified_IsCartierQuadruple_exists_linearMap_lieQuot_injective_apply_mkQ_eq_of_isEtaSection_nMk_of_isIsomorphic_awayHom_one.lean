-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d542cda5-a638-5a4e-8458-c0d0823f04b4

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_linearEquiv_lie_apply_tau_eq_of_iso
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal.Rigidified

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t t' : Rigidified p Φ κ) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q')
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hc' : t'.IsGradedS ι ψ (Rigidified.awayHom (1 : κ))) (hcb' : t'.IsGradedSbar ι ψ (Rigidified.awayHom (1 : κ)))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : κ)))
    (L : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).IsCanonicalLMap L)
    (L' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M →+ ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').NMod) (hL' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').IsCanonicalLMap L') :
    ∃ τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot,
      Function.Injective τ ∧
      ∀ (i : Fin 2) (m : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).M) (m' : ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').M) (v : Fin 2 → ℚ_[p]),
        t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : κ)) hc hcb hcΦg L hL i (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).nMk (m, 0)) v →
        t'.IsEtaSection ι hcΦ rΦ ψ hOD' (Rigidified.awayHom (1 : κ)) hc' hcb' hcΦg L' hL' i (((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').nMk (m', 0)) v →
        τ (((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).vRange.mkQ m) = ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').vRange.mkQ m' := by
  classical

  have hM : Submonoid.powers (1 : κ) ≤ IsUnit.submonoid κ := by
    rw [Submonoid.powers_one]; exact bot_le
  let eκ : κ ≃ₐ[κ] Rigidified.Baway (1 : κ) :=
    IsLocalization.atUnits (R := κ) (M := Submonoid.powers (1 : κ)) (S := Rigidified.Baway (1 : κ)) hM
  haveI : Nontrivial (Rigidified.Baway (1 : κ)) := eκ.injective.nontrivial
  haveI : CharP (Rigidified.Baway (1 : κ)) p :=
    charP_of_injective_algebraMap (algebraMap κ (Rigidified.Baway (1 : κ))).injective p
  have heκ : ∀ x : κ, eκ x = Rigidified.awayHom (1 : κ) x := fun x => by
    show eκ x = algebraMap κ _ x
    rw [Algebra.algebraMap_eq_smul_one, ← map_one eκ, ← map_smul, smul_eq_mul, mul_one]

  obtain ⟨-, τ₀, τ₁, hV⟩ := (Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ψ t Q).1 hQ
  obtain ⟨-, τ₀', τ₁', hV'⟩ := (Rigidified.isCartierQuadruple_iff_exists_via ι hcΦ rΦ ψ t' Q').1 hQ'
  obtain ⟨e⟩ := id hiso

  obtain ⟨σ, hσ0, hσ1⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_linearEquiv_lie_apply_tau_eq_of_iso
      p k ι Φ ψ t t' ht.1.1 ht'.1.1 Q Q' τ₀ τ₁ τ₀' τ₁' e

  obtain ⟨Λ, hΛ, hΛw⟩ := CerednikDrinfeld.FormalODModule.exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (t.XS (Rigidified.awayHom (1 : κ))) hc
  obtain ⟨Λ', hΛ', hΛw'⟩ := CerednikDrinfeld.FormalODModule.exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) (t'.XS (Rigidified.awayHom (1 : κ))) hc'

  let σf : (Fin 2 → Rigidified.Baway (1 : κ)) → (Fin 2 → Rigidified.Baway (1 : κ)) :=
    fun w l => eκ (σ (fun j => eκ.symm (w j)) l)
  have hσf_add : ∀ w w', σf (w + w') = σf w + σf w' := by
    intro w w'; funext l
    have hh : (fun j => eκ.symm ((w + w') j)) = (fun j => eκ.symm (w j)) + (fun j => eκ.symm (w' j)) := by
      funext j; simp [map_add]
    show eκ (σ (fun j => eκ.symm ((w + w') j)) l) = eκ (σ (fun j => eκ.symm (w j)) l) + eκ (σ (fun j => eκ.symm (w' j)) l)
    rw [hh, map_add, Pi.add_apply, map_add]
  have hσf_smul : ∀ (c : Rigidified.Baway (1 : κ)) w, σf (c • w) = c • σf w := by
    intro c w; funext l
    simp only [σf, Pi.smul_apply, smul_eq_mul]
    have : (fun j => eκ.symm (c * w j)) = eκ.symm c • (fun j => eκ.symm (w j)) := by
      funext j; simp [map_mul, Pi.smul_apply, smul_eq_mul]
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.apply_symm_apply]
  let σ₁ : (Fin 2 → Rigidified.Baway (1 : κ)) →ₗ[Rigidified.Baway (1 : κ)] (Fin 2 → Rigidified.Baway (1 : κ)) :=
    { toFun := σf, map_add' := hσf_add, map_smul' := hσf_smul }
  have hσ₁ : ∀ w, σ₁ w = σf w := fun _ => rfl
  have hσ₁_inj : Function.Injective σ₁ := by
    intro w w' h
    have h' : ∀ l, eκ (σ (fun j => eκ.symm (w j)) l) = eκ (σ (fun j => eκ.symm (w' j)) l) := fun l => congr_fun h l
    have h2 : σ (fun j => eκ.symm (w j)) = σ (fun j => eκ.symm (w' j)) := funext fun l => eκ.injective (h' l)
    have h3 := σ.injective h2
    funext j
    exact eκ.symm.injective (congr_fun h3 j)
  have hσ₁_apply : ∀ u : Fin 2 → κ, σ₁ (fun j => Rigidified.awayHom (1 : κ) (u j)) = fun l => Rigidified.awayHom (1 : κ) (σ u l) := by
    intro u; funext l
    have hh : (fun j => eκ.symm (Rigidified.awayHom (1 : κ) (u j))) = u := by
      funext j; rw [← heκ, AlgEquiv.symm_apply_apply]
    show eκ (σ (fun j => eκ.symm (Rigidified.awayHom (1 : κ) (u j))) l) = _
    rw [hh, heκ]

  have hΛ's : ∀ (w : WittVector p (Rigidified.Baway (1 : κ))) (u : Fin 2 → Rigidified.Baway (1 : κ)),
      Λ'.symm (w.coeff 0 • u) = w • Λ'.symm u := by
    intro w u
    apply Λ'.injective
    rw [AddEquiv.apply_symm_apply, hΛw', AddEquiv.apply_symm_apply]
  let τ : ((t.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc).LieQuot →ₗ[WittVector p (Rigidified.Baway (1 : κ))] ((t'.XS (Rigidified.awayHom (1 : κ))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : κ))) hc').LieQuot :=
    { toFun := fun q => Λ'.symm (σ₁ (Λ q))
      map_add' := fun q q' => by rw [map_add, map_add, map_add]
      map_smul' := fun w q => by
        rw [RingHom.id_apply, hΛw, map_smul, hΛ's] }
  have hτ : ∀ q, τ q = Λ'.symm (σ₁ (Λ q)) := fun _ => rfl
  refine ⟨τ, ?_, ?_⟩
  · intro q q' h
    rw [hτ, hτ] at h
    exact Λ.injective (hσ₁_inj (Λ'.symm.injective h))

  intro i m m' v hs hs'
  let x₀ : PrimeSpectrum κ := ⟨⊥, Ideal.bot_prime⟩

  suffices key : MvFormalGroup.CartierModule.tangent m' = σ₁ (MvFormalGroup.CartierModule.tangent m) by
    rw [hτ, hΛ, ← key, ← hΛ' m', AddEquiv.symm_apply_apply]
  have hb0 : ∀ b : ↥(x₀.asIdeal.primeCompl), (b : κ) ≠ 0 := fun b hb => b.2 (Ideal.mem_bot.mpr hb)
  obtain rfl | rfl : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | n, hi⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  · obtain ⟨hv, s, b, hu, hb, htan⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
        p k ι Φ hcΦ rΦ ψ t Q τ₀ τ₁ hV hOD hc hcb hcΦg L hL x₀ m v hs
    obtain ⟨hv', s', b', hu', hb', htan'⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uZero_eq_mk_and_awayHom_tauZero_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
        p k ι Φ hcΦ rΦ ψ t' Q' τ₀' τ₁' hV' hOD' hc' hcb' hcΦg L' hL' x₀ m' v hs'
    have hcmp := e.τ₀_u₀ x₀ v hv hv'
    have hmap : LocalizedModule.map x₀.asIdeal.primeCompl e.τ₀.toLinearMap (LocalizedModule.mk s b) = LocalizedModule.mk (e.τ₀ s) b :=
      IsLocalizedModule.map_LocalizedModules _ _ _ _
    rw [hu, hu', hmap, LocalizedModule.mk_eq] at hcmp
    obtain ⟨c, hc2⟩ := hcmp

    have h1 : (b : κ) • s' = (b' : κ) • e.τ₀ s := by
      have := smul_right_injective Q'.T₀ (hb0 c)
      apply this
      simpa [Submonoid.smul_def] using hc2

    have h2 : ∀ l : Fin 2, (b : κ) * ((τ₀' s' : ↥(t'.X.lieZero (structureMap ι ψ))) : t'.X.Lie) l =
        (b' : κ) * σ ((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) l := by
      intro l
      have := congr_arg (fun y : Q'.T₀ => ((τ₀' y : ↥(t'.X.lieZero (structureMap ι ψ))) : t'.X.Lie) l) h1
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
      rw [this, hσ0]
    funext l
    have e3 := congr_arg (Rigidified.awayHom (1 : κ)) (h2 l)
    rw [map_mul, map_mul, htan'] at e3
    have e4 : Rigidified.awayHom (1 : κ) (σ ((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) l) =
        σ₁ (fun j => Rigidified.awayHom (1 : κ) (((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) j)) l := by
      rw [hσ₁_apply]
    have e5 : (fun j => Rigidified.awayHom (1 : κ) (((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) j)) =
        Rigidified.awayHom (1 : κ) (b : κ) • MvFormalGroup.CartierModule.tangent m := by
      funext j; rw [htan j, Pi.smul_apply, smul_eq_mul]
    rw [e4, e5, map_smul, Pi.smul_apply, smul_eq_mul] at e3

    have e6 : Rigidified.awayHom (1 : κ) (b : κ) * (Rigidified.awayHom (1 : κ) (b' : κ) * MvFormalGroup.CartierModule.tangent m' l) =
        Rigidified.awayHom (1 : κ) (b : κ) * (Rigidified.awayHom (1 : κ) (b' : κ) * σ₁ (MvFormalGroup.CartierModule.tangent m) l) := by
      rw [e3]; ring
    exact hb'.mul_left_cancel (hb.mul_left_cancel e6)
  · obtain ⟨hv, s, b, hu, hb, htan⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
        p k ι Φ hcΦ rΦ ψ t Q τ₀ τ₁ hV hOD hc hcb hcΦg L hL x₀ m v hs
    obtain ⟨hv', s', b', hu', hb', htan'⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_uOne_eq_mk_and_awayHom_tauOne_eq_mul_tangent_of_isEtaSection_nMk_awayHom_one
        p k ι Φ hcΦ rΦ ψ t' Q' τ₀' τ₁' hV' hOD' hc' hcb' hcΦg L' hL' x₀ m' v hs'
    have hcmp := e.τ₁_u₁ x₀ v hv hv'
    have hmap : LocalizedModule.map x₀.asIdeal.primeCompl e.τ₁.toLinearMap (LocalizedModule.mk s b) = LocalizedModule.mk (e.τ₁ s) b :=
      IsLocalizedModule.map_LocalizedModules _ _ _ _
    rw [hu, hu', hmap, LocalizedModule.mk_eq] at hcmp
    obtain ⟨c, hc2⟩ := hcmp
    have h1 : (b : κ) • s' = (b' : κ) • e.τ₁ s := by
      have := smul_right_injective Q'.T₁ (hb0 c)
      apply this
      simpa [Submonoid.smul_def] using hc2
    have h2 : ∀ l : Fin 2, (b : κ) * ((τ₁' s' : ↥(t'.X.lieOne (structureMap ι ψ))) : t'.X.Lie) l =
        (b' : κ) * σ ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) l := by
      intro l
      have := congr_arg (fun y : Q'.T₁ => ((τ₁' y : ↥(t'.X.lieOne (structureMap ι ψ))) : t'.X.Lie) l) h1
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
      rw [this, hσ1]
    funext l
    have e3 := congr_arg (Rigidified.awayHom (1 : κ)) (h2 l)
    rw [map_mul, map_mul, htan'] at e3
    have e4 : Rigidified.awayHom (1 : κ) (σ ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) l) =
        σ₁ (fun j => Rigidified.awayHom (1 : κ) (((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) j)) l := by
      rw [hσ₁_apply]
    have e5 : (fun j => Rigidified.awayHom (1 : κ) (((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) j)) =
        Rigidified.awayHom (1 : κ) (b : κ) • MvFormalGroup.CartierModule.tangent m := by
      funext j; rw [htan j, Pi.smul_apply, smul_eq_mul]
    rw [e4, e5, map_smul, Pi.smul_apply, smul_eq_mul] at e3
    have e6 : Rigidified.awayHom (1 : κ) (b : κ) * (Rigidified.awayHom (1 : κ) (b' : κ) * MvFormalGroup.CartierModule.tangent m' l) =
        Rigidified.awayHom (1 : κ) (b : κ) * (Rigidified.awayHom (1 : κ) (b' : κ) * σ₁ (MvFormalGroup.CartierModule.tangent m) l) := by
      rw [e3]; ring
    exact hb'.mul_left_cancel (hb.mul_left_cancel e6)

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearMap_lieQuot_injective_apply_mkQ_eq_of_isEtaSection_nMk_of_isIsomorphic_awayHom_one (solution)
