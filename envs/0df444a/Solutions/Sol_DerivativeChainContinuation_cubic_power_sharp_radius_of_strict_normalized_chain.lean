-- Prove2me | solution 1 for DerivativeChainContinuation.cubic_power_sharp_radius_of_strict_normalized_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:13:11.639831+00:00
-- url     : https://prove2.me/submissions/1230fe17-3e49-4c82-ba4f-450f6781bae6

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_cubic_power_nonzero_sharp
import Theorems.Thm_DerivativeChainContinuation_cubic_power_zero_moment_sharp
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainContinuation in
theorem solution (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree=3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x=0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by
  classical
  have hnonzero := cubic_power_nonzero_sharp h hh a b ha hb last hlast hstrict
  have hcard : q.roots.card=3 := by rw [← (IsAlgClosed.splits q).natDegree_eq_card_roots,hdeg]
  obtain ⟨u,v,w,hroots⟩ := Multiset.card_eq_three.mp hcard
  have hfactor : q=(X-C u)*(X-C v)*(X-C w) := by
    rw [(IsAlgClosed.splits q).eq_prod_roots_of_monic hq,hroots]
    simp [mul_assoc]
  have hu : ‖u-o‖ ≤ R := hbound u ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hv : ‖v-o‖ ≤ R := hbound v ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hw : ‖w-o‖ ≤ R := hbound w ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hsol := if hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0 then
      hnonzero u v w o R hu hv hw hA
    else cubic_power_zero_moment_sharp h hh last hlast hnonzero u v w o R hR hu hv hw (by simpa using hA)
  obtain ⟨z,A,B,hzroot,hstart,htail,hend,hA,hB,horth,hmA,hmB,hcost⟩ := hsol
  refine ⟨z,A,B,?_,?_,htail,?_,hA,hB,horth,hmA,hmB,hcost⟩
  · simpa only [hfactor] using hzroot
  · simpa [hroots,add_assoc] using hstart
  · simpa only [hfactor] using hend
