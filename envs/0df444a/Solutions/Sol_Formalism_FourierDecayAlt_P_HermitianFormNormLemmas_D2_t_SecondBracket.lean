-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2.t_SecondBracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:15.284797+00:00
-- url     : https://prove2.me/submissions/327da994-ce47-4c3c-85c9-843dc1ff1403

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2
theorem _root_.solution : SecondBracket := by
  intro Cl Γ Nu isPt a2 w Jloc JB n NG ND Hh ngen κ2 cSt AAre e1 gf Pc TB e7 eN Aexp
    hκ hcSt hAA he1 hgf hPc hexp ha2 hpt hmean hmeas hmass hheight hTB T hT
  have hmaps : ∀ x ∈ T, x.2.1 ∈ T.image (fun x => x.2.1) := fun x hx => mem_image_of_mem _ hx
  rw [← sum_fiberwise_of_maps_to hmaps]
  set K : ℝ := κ2 * cSt * AAre * e1 * Pc * gf ^ Aexp with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hptI : ∀ γ ∈ T.image (fun x => x.2.1), isPt γ := by
    intro γ hγ
    obtain ⟨x0, hx0, rfl⟩ := mem_image.mp hγ
    exact hT x0 hx0
  have hfin : ∑ γ ∈ T.image (fun x => x.2.1), K * (w γ * n γ * (NG γ * ND γ) ^ Aexp * JB γ) ≤ K * TB := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (hTB _ hptI) hK0
  refine le_trans (sum_le_sum ?_) hfin
  intro γ hγ
  have hp := hptI γ hγ
  obtain ⟨hw, hJl, hJB, hn, hNG, hND, hH⟩ := hpt γ hp

  have hinner : ∑ x ∈ T with x.2.1 = γ, (w x.2.1 * (Pc * NG x.2.1 ^ 6)) * (a2 x.1 x.2.1 x.2.2 * Jloc x.2.1) =
      (w γ * (Pc * NG γ ^ 6) * Jloc γ) *
        ∑ y ∈ (T.filter (fun x => x.2.1 = γ)).image (fun x => (x.1, x.2.2)), a2 y.1 γ y.2 := by
    rw [sum_image]
    · rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [(mem_filter.mp hx).2]
      ring
    · intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_coe.mp ha)).2
      have hb' := (mem_filter.mp (mem_coe.mp hb)).2
      have hab' : (a.1, a.2.2) = (b.1, b.2.2) := hab
      have h1 : a.1 = b.1 := (Prod.mk.inj hab').1
      have h2 : a.2.2 = b.2.2 := (Prod.mk.inj hab').2
      exact Prod.ext h1 (Prod.ext (ha'.trans hb'.symm) h2)
  rw [hinner]
  set σ : ℝ := ∑ y ∈ (T.filter (fun x => x.2.1 = γ)).image (fun x => (x.1, x.2.2)), a2 y.1 γ y.2 with hσ
  have hσ0 : 0 ≤ σ := sum_nonneg (fun y _ => ha2 _ _ _)
  have hH0 : 0 ≤ Hh γ := by linarith
  have hσ1 : σ ≤ κ2 * Hh γ ^ e7 * (AAre * e1 * Hh γ ^ eN * n γ) := by
    refine le_trans (hmean γ hp _) ?_
    exact mul_le_mul_of_nonneg_left (hmass γ hp) (by positivity)
  have hNG0 : 0 ≤ NG γ := by linarith
  have hND0 : 0 ≤ ND γ := by linarith
  have hF : w γ * (Pc * NG γ ^ 6) * Jloc γ ≤ w γ * (Pc * NG γ ^ 6) * (cSt * JB γ) :=
    mul_le_mul_of_nonneg_left (hmeas γ hp) (by positivity)
  have hstep : (w γ * (Pc * NG γ ^ 6) * Jloc γ) * σ ≤
      (w γ * (Pc * NG γ ^ 6) * (cSt * JB γ)) * (κ2 * Hh γ ^ e7 * (AAre * e1 * Hh γ ^ eN * n γ)) :=
    mul_le_mul hF hσ1 hσ0 (by positivity)
  refine le_trans hstep ?_

  set Xx : ℝ := NG γ * ND γ with hX
  have hX1 : 1 ≤ Xx := by rw [hX]; nlinarith
  have hX0 : 0 ≤ Xx := by linarith
  have hNGX : NG γ ≤ Xx := by rw [hX]; nlinarith
  have hHX : Hh γ ≤ gf * Xx := by rw [hX, ← mul_assoc]; exact hheight γ hp
  have hgf0 : 0 ≤ gf := by linarith
  have hpw : NG γ ^ 6 * (Hh γ ^ e7 * Hh γ ^ eN) ≤ gf ^ Aexp * Xx ^ Aexp := by
    rw [← pow_add]
    calc NG γ ^ 6 * Hh γ ^ (e7 + eN) ≤ Xx ^ 6 * (gf * Xx) ^ (e7 + eN) := by gcongr
      _ = gf ^ (e7 + eN) * Xx ^ (e7 + eN + 6) := by rw [mul_pow, pow_add Xx]; ring
      _ ≤ gf ^ Aexp * Xx ^ Aexp := by
          apply mul_le_mul (pow_le_pow_right₀ hgf (by omega)) (pow_le_pow_right₀ hX1 hexp)
            (by positivity) (by positivity)
  have hrest : 0 ≤ w γ * Pc * cSt * JB γ * κ2 * AAre * e1 * n γ := by positivity
  calc (w γ * (Pc * NG γ ^ 6) * (cSt * JB γ)) * (κ2 * Hh γ ^ e7 * (AAre * e1 * Hh γ ^ eN * n γ))
      = (w γ * Pc * cSt * JB γ * κ2 * AAre * e1 * n γ) * (NG γ ^ 6 * (Hh γ ^ e7 * Hh γ ^ eN)) := by ring
    _ ≤ (w γ * Pc * cSt * JB γ * κ2 * AAre * e1 * n γ) * (gf ^ Aexp * Xx ^ Aexp) :=
        mul_le_mul_of_nonneg_left hpw hrest
    _ = K * (w γ * n γ * Xx ^ Aexp * JB γ) := by rw [hK]; ring
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2
