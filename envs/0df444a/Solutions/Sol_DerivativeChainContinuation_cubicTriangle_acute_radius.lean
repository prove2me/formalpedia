-- Prove2me | solution 1 for DerivativeChainContinuation.cubicTriangle_acute_radius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:17:46.641763+00:00
-- url     : https://prove2.me/submissions/18c9642c-9be9-4dd6-810a-c82937596313

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicCertificate
import Definitions.Def_DerivativeChainContinuation_SharpCubicTriangle
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_three_point_radius_lower_bound
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation





theorem cubicTriangle_sides (k s : ℝ) :
    Complex.normSq (cubicTriangleA k s-cubicTriangleB k s)=cubicSideU k s ∧
    Complex.normSq (cubicTriangleA k s-cubicTriangleC k s)=cubicSideV k s ∧
    Complex.normSq (cubicTriangleB k s-cubicTriangleC k s)=cubicSideW k s := by
  simp only [cubicTriangleA,cubicTriangleB,cubicTriangleC,cubicSideU,cubicSideV,cubicSideW,
    Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  constructor
  · ring
  constructor <;> ring



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (k s : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hs : 1 ≤ s) (hs3 : s^2 ≤ 3) (o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ‖cubicTriangleA k s-o‖ ≤ R) (hb : ‖cubicTriangleB k s-o‖ ≤ R)
    (hc : ‖cubicTriangleC k s-o‖ ≤ R) :
    cubicSideU k s*cubicSideV k s*cubicSideW k s ≤ s^2*(k^2+3)^2*R^2 := by
  obtain ⟨hU,hV,hW⟩ := cubicTriangle_sides k s
  have harea : 2*(cubicSideU k s*cubicSideV k s+cubicSideU k s*cubicSideW k s+
      cubicSideV k s*cubicSideW k s)-(cubicSideU k s)^2-(cubicSideV k s)^2-
      (cubicSideW k s)^2 = s^2*(k^2+3)^2 := by
    unfold cubicSideU cubicSideV cubicSideW; ring
  have hVU : 0 ≤ cubicSideV k s-cubicSideU k s := by
    have he : cubicSideV k s-cubicSideU k s = k*(3-s^2) := by
      unfold cubicSideU cubicSideV; ring
    rw [he]; exact mul_nonneg hk (sub_nonneg.mpr hs3)
  have hVW : 0 ≤ cubicSideV k s-cubicSideW k s := by
    have he : cubicSideV k s-cubicSideW k s = (3-k)*(k+1)*(3-s^2)/4 := by
      unfold cubicSideV cubicSideW; ring
    rw [he]
    have h1 : 0 ≤ 3-k := by linarith
    have h2 : 0 ≤ k+1 := by linarith
    have h3 : 0 ≤ 3-s^2 := by linarith
    positivity
  have hUWV : 0 ≤ cubicSideU k s+cubicSideW k s-cubicSideV k s := by
    have he : cubicSideU k s+cubicSideW k s-cubicSideV k s =
        (1-k)^2+(k+1)*(s^2-1) := by unfold cubicSideU cubicSideV cubicSideW; ring
    rw [he]
    have h1 : 0 ≤ k+1 := by linarith
    have h2 : 0 ≤ s^2-1 := by nlinarith
    positivity
  have hU0 : 0 ≤ cubicSideU k s := by unfold cubicSideU; positivity
  have hW0 : 0 ≤ cubicSideW k s := by unfold cubicSideW; positivity
  have h := three_point_radius_lower_bound (cubicTriangleA k s) (cubicTriangleB k s)
    (cubicTriangleC k s) o R _ _ _ hR ha hb hc hU hV hW
    (by linarith) hUWV (by linarith) (by rw [harea]; positivity)
  rwa [harea] at h
