-- Prove2me | solution 1 for Formalism.LT.LTL.frob_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:48.088818+00:00
-- url     : https://prove2.me/submissions/ebe04b11-12f2-4f98-83ae-26501076edcb

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_P2M_Formalism_LT_LTL_norm_le_of_mem_span__3b10f192d90f
import Theorems.Thm_P2M_Formalism_LT_LTL_mem_span_of_norm_le__498e07ccaf2e
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
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.LTL
theorem _root_.solution {ι : Type*} (p h : ℕ) (hpr : p.Prime) (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hp : ‖(p : K)‖ ≤ ‖π‖) (hF : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ (p ^ h) - a‖ ≤ ‖π‖)
    (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    DivByMv π (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A) := by
  have := Fact.mk hpr
  have hπ : ‖π‖ ≤ 1 := hπ1.le
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  set O := unitBall K
  set I : Ideal O := Ideal.span {piO π hπ}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : O) ∈ I := htop ▸ Submodule.mem_top
    have := norm_le_of_mem_span' hπ 1 h1
    simp at this
    linarith
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hpI : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    apply mem_span_of_norm_le' hπ hπne
    simpa using hp
  have : CharP (O ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpr).mpr hpI
  have : ExpChar (O ⧸ I) p := ExpChar.prime hpr
  set mk := Ideal.Quotient.mk I
  set A' := Formalism.LT.FrobP.liftO A hA
  set B' : MvPowerSeries ι O := A' ^ (p ^ h) - MvPowerSeries.expand (p ^ h)
    (pow_ne_zero h hpr.ne_zero) A'
  have hB : A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A =
      MvPowerSeries.map O.subtype B' := by
    simp only [B', map_sub, map_pow, MvPowerSeries.map_expand]
    rw [show MvPowerSeries.map O.subtype A' = A from Formalism.LT.FrobP.map_liftO A hA]
  have hcomp : (iterateFrobenius (O ⧸ I) p h).comp mk = mk := by
    ext a
    simp only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    rw [Ideal.Quotient.eq]
    apply mem_span_of_norm_le' hπ hπne
    exact hF a.1 a.2
  have hzero : MvPowerSeries.map mk B' = 0 := by
    simp only [B', map_sub, map_pow, MvPowerSeries.map_expand]
    rw [← MvPowerSeries.map_iterateFrobenius_expand _ hpr.ne_zero, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_map, hcomp, sub_self]
  intro d
  rw [hB, MvPowerSeries.coeff_map]
  apply norm_le_of_mem_span' hπ
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (MvPowerSeries.coeff d) hzero
  simpa [MvPowerSeries.coeff_map] using this
end Formalism.LT.LTL
