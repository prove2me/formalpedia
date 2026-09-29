-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/95210f0e-55bc-5ae6-bea5-bde3e8ca0427

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal.Rigidified

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t.IsCartierQuadruple ι hcΦ rΦ ψ Q') :
    Q.IsIsomorphic Q' := by
  classical
  obtain ⟨hOD, τ₀, τ₁, hT0, hT1, H⟩ := hQ
  obtain ⟨-, τ₀', τ₁', hT0', hT1', H'⟩ := hQ'
  have HN0 : ∀ x, Q.N₀ x = Q'.N₀ x := fun x =>
    Submodule.ext fun v => ((H hOD x).1 v).trans ((H' hOD x).1 v).symm
  have HN1 : ∀ x, Q.N₁ x = Q'.N₁ x := fun x =>
    Submodule.ext fun v => ((H hOD x).2.1 v).trans ((H' hOD x).2.1 v).symm
  refine ⟨{ N₀_eq := HN0, N₁_eq := HN1, τ₀ := τ₀.trans τ₀'.symm, τ₁ := τ₁.trans τ₁'.symm,
            τ₁_Pi₀ := ?_, τ₀_Pi₁ := ?_, τ₀_u₀ := ?_, τ₁_u₁ := ?_ }⟩
  · intro s
    apply τ₁'.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hT0, hT0', LinearEquiv.apply_symm_apply]
  · intro s
    apply τ₀'.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hT1, hT1', LinearEquiv.apply_symm_apply]
  · intro x v hv hv'
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := ((H hOD x).1 v).1 hv
    obtain ⟨m, s, b, hm, hu, hco⟩ := (H hOD x).2.2.1 v hv f hf hc hcb hcΦf L hL z hz
    obtain ⟨m', s', b', hm', hu', hco'⟩ := (H' hOD x).2.2.1 v hv' f hf hc hcb hcΦf L hL z hz
    have htan : tangent m = tangent m' := by
      have hmm : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m' := hm.trans hm'.symm
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hmm
      obtain ⟨y, hy⟩ := hmm
      have h2 := congrArg tangent hy
      erw [tangent_verschiebungInt] at h2
      have h3 : tangent m - tangent m' = 0 := by rw [← map_sub]; exact h2.symm
      exact sub_eq_zero.1 h3
    rw [hu', hu, LocalizedModule.map_mk]

    have hcoord : ∀ i, ∃ c : x.asIdeal.primeCompl,
        (c : B) * (((τ₀ s : _) : t.X.Lie) i * (b' : B)) = (c : B) * (((τ₀' s' : _) : t.X.Lie) i * (b : B)) := by
      intro i
      have h1 := hco i
      have h2 := hco' i
      rw [← htan] at h2
      have h3 : locHom x ((((τ₀ s : _) : t.X.Lie) i) * (b' : B)) =
          locHom x ((((τ₀' s' : _) : t.X.Lie) i) * (b : B)) := by
        rw [map_mul, map_mul, h1, h2]; ring
      exact (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Bloc x)).1 h3
    obtain ⟨c0, hc0⟩ := hcoord 0
    obtain ⟨c1, hc1⟩ := hcoord 1
    rw [LocalizedModule.mk_eq]
    refine ⟨c0 * c1, ?_⟩
    apply τ₀'.injective
    apply Subtype.ext
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
      simp only [Submonoid.smul_def, map_smul, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submonoid.coe_mul]
    · linear_combination (-(c1 : B)) * hc0
    · linear_combination (-(c0 : B)) * hc1
  · intro x v hv hv'
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := ((H hOD x).2.1 v).1 hv
    obtain ⟨m, s, b, hm, hu, hco⟩ := (H hOD x).2.2.2 v hv f hf hc hcb hcΦf L hL z hz
    obtain ⟨m', s', b', hm', hu', hco'⟩ := (H' hOD x).2.2.2 v hv' f hf hc hcb hcΦf L hL z hz
    have htan : tangent m = tangent m' := by
      have hmm : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m' := hm.trans hm'.symm
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hmm
      obtain ⟨y, hy⟩ := hmm
      have h2 := congrArg tangent hy
      erw [tangent_verschiebungInt] at h2
      have h3 : tangent m - tangent m' = 0 := by rw [← map_sub]; exact h2.symm
      exact sub_eq_zero.1 h3
    rw [hu', hu, LocalizedModule.map_mk]

    have hcoord : ∀ i, ∃ c : x.asIdeal.primeCompl,
        (c : B) * (((τ₁ s : _) : t.X.Lie) i * (b' : B)) = (c : B) * (((τ₁' s' : _) : t.X.Lie) i * (b : B)) := by
      intro i
      have h1 := hco i
      have h2 := hco' i
      rw [← htan] at h2
      have h3 : locHom x ((((τ₁ s : _) : t.X.Lie) i) * (b' : B)) =
          locHom x ((((τ₁' s' : _) : t.X.Lie) i) * (b : B)) := by
        rw [map_mul, map_mul, h1, h2]; ring
      exact (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Bloc x)).1 h3
    obtain ⟨c0, hc0⟩ := hcoord 0
    obtain ⟨c1, hc1⟩ := hcoord 1
    rw [LocalizedModule.mk_eq]
    refine ⟨c0 * c1, ?_⟩
    apply τ₁'.injective
    apply Subtype.ext
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
      simp only [Submonoid.smul_def, map_smul, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submonoid.coe_mul]
    · linear_combination (-(c1 : B)) * hc0
    · linear_combination (-(c0 : B)) * hc1

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic (solution)
