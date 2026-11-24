-- Prove2me | solution 1 for Formalism.LT.FrobP.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:32.592312+00:00
-- url     : https://prove2.me/submissions/7cf23235-c455-4fe2-9a84-1d5c5a7e312f

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Theorems.Thm_Formalism_LT_FrobP_norm_le_of_mem_span
import Theorems.Thm_Formalism_LT_FrobP_mem_span_of_norm_le
import Theorems.Thm_Formalism_LT_FrobP_natCast_nonunit
import Theorems.Thm_Formalism_LT_FrobP_map_liftO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.FrobP
theorem _root_.solution {ι : Type v} (p h : ℕ) (hpr : p.Prime) (σ : K →+* K) (hp0 : (p : K) ≠ 0)
    (hp : ‖(p : K)‖ < 1) (hσ : IsFrobLift p (p ^ h) σ) (A : MvPowerSeries ι K)
    (hA : IntegralMv A) :
    DivByMv (p : K) (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero)
      (MvPowerSeries.map σ A)) := by
  classical
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI hchar : CharP (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p :=
    CharP.quotient (unitBall K) p (natCast_nonunit hp)
  haveI : ExpChar (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p := ExpChar.prime hpr
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have hkey : (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})).comp (sigmaO hσ hp)
      = (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h).comp
          (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    first
      | rw [Ideal.Quotient.eq]
      | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply mem_span_of_norm_le hp0
    first
      | exact hσ c.1 c.2
      | (push_cast; exact hσ c.1 c.2)
  have h1 : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h)
        (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) (liftO A hA)) := by
    ext d
    simp only [MvPowerSeries.coeff_map]
    exact RingHom.congr_fun hkey _
  have hmain : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
      ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) = 0 := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h1, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_iterateFrobenius_expand p hpr.ne_zero, sub_self]
  have hcoeffI : ∀ d, MvPowerSeries.coeff d ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
      (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
    intro d
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPowerSeries.coeff_map, hmain, map_zero]
  have h2 : MvPowerSeries.map (unitBall K).subtype (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map σ A := by
    ext d
    first
      | rfl
      | (simp only [MvPowerSeries.coeff_map]; rfl)
  have hsub : MvPowerSeries.map (unitBall K).subtype ((liftO A hA) ^ (p ^ h)
      - MvPowerSeries.expand (p ^ h) hq (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA)))
      = A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) (MvPowerSeries.map σ A) := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h2, map_liftO]
  intro d
  rw [← hsub, MvPowerSeries.coeff_map]
  exact norm_le_of_mem_span (p := p) _ (hcoeffI d)
end Formalism.LT.FrobP
