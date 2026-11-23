-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.hensel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:47.225964+00:00
-- url     : https://prove2.me/submissions/0bb644b7-fac1-48ad-a6a0-35cfc4cd357c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_approx_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_pow_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) (s : ℕ) {θ : K} (hθ : (s : K) * θ = 1) {a : ℕ}
    (ha : θ ∈ Pk R ϖ (-(a : ℤ))) {n : ℤ} (hn : (a : ℤ) + 1 ≤ n) {y : K} (hy : y ∈ Pk R ϖ n) :
    ∃ v ∈ R, (1 + y * v) ^ s = 1 + (s : K) * y := by
  have hn0 : 0 ≤ n := by omega
  have happ : ∀ k : ℕ, ∃ w ∈ Pk R ϖ n,
      y - w - θ * ((1 + w) ^ s - 1 - (s : K) * w) ∈ Pk R ϖ (n + k) := by
    intro k
    induction k with
    | zero => exact ⟨0, (Pk R ϖ n).zero_mem, by simpa using hy⟩
    | succ k ih =>
      obtain ⟨w, hw, he⟩ := ih
      set e := y - w - θ * ((1 + w) ^ s - 1 - (s : K) * w) with hedef
      have hw' : w + e ∈ Pk R ϖ n := (Pk R ϖ n).add_mem hw (Pk_mono h.mem (by omega) he)
      obtain ⟨g, hg, hgeq⟩ := pow_diff h hn0 s hw hw'
      refine ⟨w + e, hw', ?_⟩
      have hcalc : y - (w + e) - θ * ((1 + (w + e)) ^ s - 1 - (s : K) * (w + e)) =
          -(θ * (e * g)) := by
        have h1 : (1 + (w + e)) ^ s = (1 + w) ^ s + e * ((s : K) + g) := by
          have : w + e - w = e := by ring
          rw [this] at hgeq
          linear_combination hgeq
        rw [h1]
        linear_combination (-1 : K) * hedef
      rw [hcalc]
      refine (Pk R ϖ _).neg_mem ?_
      have := Pk_mul ha (Pk_mul he hg)
      exact Pk_mono h.mem (by push_cast; omega) this
  obtain ⟨w, hw, hw0⟩ := approx_zero h (Pk_isCompact h n)
    (f := fun w => y - w - θ * ((1 + w) ^ s - 1 - (s : K) * w)) (by fun_prop)
    (fun k => by
      obtain ⟨w, hw, he⟩ := happ k
      exact ⟨w, hw, Pk_mono h.mem (by omega) he⟩)
  obtain ⟨g, hg, hgeq⟩ := pow_diff h hn0 s (Pk R ϖ n).zero_mem hw
  simp only [add_zero, one_pow, sub_zero] at hgeq
  have hθg : θ * g ∈ Pk R ϖ 1 := Pk_mono h.mem (by omega) (Pk_mul ha hg)
  obtain ⟨v, hv, hv1⟩ := inv_one_add h hθg
  have hy' : y = w * (1 + θ * g) := by
    have : (1 + w) ^ s - 1 - (s : K) * w = w * g := by linear_combination hgeq
    rw [this] at hw0
    linear_combination hw0
  have hyv : y * v = w := by
    rw [hy', mul_assoc, hv1, mul_one]
  refine ⟨v, hv, ?_⟩
  rw [hyv, hy']
  linear_combination hgeq - w * g * hθ
end Formalism.FourierDecayAlt.P.HenselRootsBounded
