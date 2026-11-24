-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.seminormOfForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:23.98703+00:00
-- url     : https://prove2.me/submissions/a05125ce-aa54-44c8-b558-e5b193d86d04

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_ccMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux8
private theorem sqrt_add_le_sqrt_add_sqrt_of_quadratic_nonneg {Qv Qw R : ℝ} (hv : 0 ≤ Qv) (hw : 0 ≤ Qw)
    (h : ∀ t : ℝ, 0 ≤ Qw * (t * t) + R * t + Qv) : Real.sqrt (Qv + R + Qw) ≤ Real.sqrt Qv + Real.sqrt Qw := by
  have hd := discrim_le_zero h
  unfold discrim at hd
  have h1 := Real.sq_sqrt hv
  have h2 := Real.sq_sqrt hw
  have ha := Real.sqrt_nonneg Qv
  have hb := Real.sqrt_nonneg Qw
  have hs : 0 ≤ Real.sqrt Qv + Real.sqrt Qw := add_nonneg ha hb
  have e : (2 * (Real.sqrt Qv * Real.sqrt Qw)) ^ 2 = 4 * Qw * Qv := by
    rw [mul_pow, mul_pow, h1, h2]; ring
  have hR : R ≤ 2 * (Real.sqrt Qv * Real.sqrt Qw) := by
    by_contra hc
    push_neg at hc
    have hp : 0 ≤ 2 * (Real.sqrt Qv * Real.sqrt Qw) := by positivity
    nlinarith
  rw [← Real.sqrt_sq hs]
  apply Real.sqrt_le_sqrt
  nlinarith
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V)
end
section supp
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pi
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
end pi
end supp
end Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : SeminormOfForm := by
  intro k ρ E _ _ bet a AB Cp mmB S hAB hCp hPos hLB V _ _ M
  obtain ⟨hSes, hPP⟩ := hPos
  obtain ⟨hadd1, hadd2, hsm1, hsm2⟩ := hSes
  have hC : ∀ v, CCS a mmB S (M.ev v) := fun v => ⟨⟨‖v‖, M.mem v⟩, M.off v⟩
  have hQ0 : ∀ v, 0 ≤ (bet (M.ev v) (M.ev v)).re := fun v => (hPP _ (hC v)).2
  have key : ∀ v w : V, ∀ t : ℝ, (bet (M.ev (v + (t : ℂ) • w)) (M.ev (v + (t : ℂ) • w))).re =
      (bet (M.ev v) (M.ev v)).re + t * (bet (M.ev v) (M.ev w) + bet (M.ev w) (M.ev v)).re +
        t * t * (bet (M.ev w) (M.ev w)).re := by
    intro v w t
    have hx := hC v
    have hy := hC w
    have hcy : CCS a mmB S ((t : ℂ) • M.ev w) := by rw [← map_smul]; exact hC _
    have hs : CCS a mmB S (M.ev v + (t : ℂ) • M.ev w) := by rw [← map_smul, ← map_add]; exact hC _
    have e1 : bet (M.ev v + (t : ℂ) • M.ev w) (M.ev v + (t : ℂ) • M.ev w) =
        bet (M.ev v) (M.ev v) + (t : ℂ) * bet (M.ev v) (M.ev w) + (t : ℂ) * bet (M.ev w) (M.ev v) +
          (t : ℂ) * ((t : ℂ) * bet (M.ev w) (M.ev w)) := by
      rw [hadd1 _ _ _ hx hcy hs, hadd2 _ _ _ hx hx hcy, hadd2 _ _ _ hcy hx hcy,
        hsm2 _ _ _ hx hy, hsm1 _ _ _ hy hx, hsm1 _ _ _ hy hcy, hsm2 _ _ _ hy hy, Complex.conj_ofReal]
      ring
    rw [map_add, map_smul, e1]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  have disc : ∀ v w : V, ∀ t : ℝ, 0 ≤ (bet (M.ev w) (M.ev w)).re * (t * t) +
      (bet (M.ev v) (M.ev w) + bet (M.ev w) (M.ev v)).re * t + (bet (M.ev v) (M.ev v)).re := by
    intro v w t
    have h := hQ0 (v + (t : ℂ) • w)
    rw [key v w t] at h
    nlinarith [h]
  refine ⟨Seminorm.of (fun v => Real.sqrt (bet (M.ev v) (M.ev v)).re) ?_ ?_, ?_, ?_⟩
  · intro v w
    show Real.sqrt (bet (M.ev (v + w)) (M.ev (v + w))).re ≤
      Real.sqrt (bet (M.ev v) (M.ev v)).re + Real.sqrt (bet (M.ev w) (M.ev w)).re
    have h1 := key v w 1
    simp only [Complex.ofReal_one, one_smul, one_mul] at h1
    rw [h1]
    exact sqrt_add_le_sqrt_add_sqrt_of_quadratic_nonneg (hQ0 v) (hQ0 w) (disc v w)
  · intro c v
    show Real.sqrt (bet (M.ev (c • v)) (M.ev (c • v))).re = ‖c‖ * Real.sqrt (bet (M.ev v) (M.ev v)).re
    have hx := hC v
    have hcx : CCS a mmB S (c • M.ev v) := by rw [← map_smul]; exact hC _
    rw [map_smul, hsm1 _ _ _ hx hcx, hsm2 _ _ _ hx hx, ← mul_assoc, Complex.mul_conj,
      Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg c), Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg c)]
  · intro v
    show Real.sqrt (bet (M.ev v) (M.ev v)).re ^ 2 = _
    exact Real.sq_sqrt (hQ0 v)
  · intro v
    show Real.sqrt (bet (M.ev v) (M.ev v)).re ≤ Cp * ‖v‖
    have hcc : B.CCle AB mmB (M.ev v) ‖v‖ := ccMono k ρ E a AB ‖v‖ mmB (M.ev v) hAB (M.mem v)
    have hb := hLB (M.ev v) ‖v‖ hcc (M.off v)
    have hre : (bet (M.ev v) (M.ev v)).re ≤ (Cp * ‖v‖) ^ 2 := le_trans (Complex.re_le_norm _) hb
    calc Real.sqrt (bet (M.ev v) (M.ev v)).re ≤ Real.sqrt ((Cp * ‖v‖) ^ 2) := Real.sqrt_le_sqrt hre
      _ = Cp * ‖v‖ := Real.sqrt_sq (mul_nonneg hCp (norm_nonneg v))
end Formalism.FourierDecayAlt.P.Ux8
