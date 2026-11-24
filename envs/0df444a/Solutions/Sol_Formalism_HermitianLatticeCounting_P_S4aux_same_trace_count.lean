-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.same_trace_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:25.063902+00:00
-- url     : https://prove2.me/submissions/eb6127e1-64fc-442d-b902-6e3a7e666ccb

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_herm_split
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_pair
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shear_inv
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : SameTrace := by
  intro E _ _ V _ _ h O La Lb r e y yb hH htr hLa hLb hIa hIb he heLa hcap hy hyb hd hdb hD
  have heLb : ∀ i, e i ∈ Lb := fun i => (hcap _ (fun k => he i k)).1 (heLa i)
  have hdj : ∀ j, ∃ l ∈ La, (∀ i, h l (e i) = 0) ∧ ∃ c : Fin r → E, yb j - y j = l + ∑ i, c i • e i := by
    intro j
    apply hD
    · intro i; rw [map_sub, LinearMap.sub_apply, hd, hdb, sub_self]
    · intro v hv hv0
      rw [map_sub]
      exact O.sub_mem (hIb _ ((hcap v hv0).1 hv) _ (hyb j)) (hIa _ hv _ (hy j))
  choose l hl hl0 c hc using hdj
  have tE : ∀ (a : Fin r → E) i, h (∑ k, a k • e k) (e i) = 0 := by
    intro a i; simp [map_sum, LinearMap.sum_apply, he]
  have Et : ∀ (a : Fin r → E) (v : V), h v (∑ k, a k • e k) = ∑ k, star (a k) * h v (e k) := by
    intro a v; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
  have tv : ∀ (a : Fin r → E) (w : V), h (∑ k, a k • e k) w = ∑ k, a k * star (h w (e k)) := by
    intro a w
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [hH w (e k)]
  have tt : ∀ (a b : Fin r → E), h (∑ k, a k • e k) (∑ k, b k • e k) = 0 := by
    intro a b
    rw [Et]
    exact Finset.sum_eq_zero fun k _ => by rw [tE, mul_zero]
  have pairing : ∀ (a : Fin r → Fin r → E) j k,
      h (y j + ∑ i, a j i • e i) (y k + ∑ i, a k i • e i) = h (y j) (y k) + (a j k + star (a k j)) := by
    intro a j k
    rw [map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, tt, Et, tv]
    simp only [hd, apply_ite (star : E → E), star_one, star_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hz : ∀ j, y j + ∑ i, c j i • e i ∈ Lb := by
    intro j
    have : y j + ∑ i, c j i • e i = yb j - l j := by
      have := hc j
      rw [sub_eq_iff_eq_add] at this
      rw [this]; abel
    rw [this]
    exact Lb.sub_mem (hyb j) ((hcap _ (hl0 j)).1 (hl j))
  obtain ⟨c', hc'O, hc'⟩ := herm_split O htr r (fun j k => c j k + star (c k j))
    (fun j k => by
      have h1 := pairing c j k
      have h2 : c j k + star (c k j) = h (y j + ∑ i, c j i • e i) (y k + ∑ i, c k i • e i) - h (y j) (y k) := by
        rw [h1]; ring
      rw [h2]
      exact O.sub_mem (hIb _ (hz j) _ (hz k)) (hIa _ (hy j) _ (hy k)))
    (fun j k => by simp [add_comm])
  obtain ⟨a, ha⟩ : ∃ a : Fin r → Fin r → E, a = fun j i => c j i - c' j i := ⟨_, rfl⟩
  have hskew : ∀ j k, a j k + star (a k j) = 0 := by
    intro j k
    simp only [ha, star_sub]
    linear_combination -(hc' j k)
  obtain ⟨t, ht⟩ : ∃ t : Fin r → V, t = fun j => ∑ i, a j i • e i := ⟨_, rfl⟩
  have htE : ∀ j i, h (t j) (e i) = 0 := fun j i => by rw [ht]; exact tE _ i
  have hntE : ∀ j i, h ((fun j => - t j) j) (e i) = 0 := fun j i => by simp [htE]
  have hzz : ∀ j, y j + t j ∈ Lb := by
    intro j
    have : y j + t j = (y j + ∑ i, c j i • e i) - ∑ i, c' j i • e i := by
      simp only [ht, ha, sub_smul, Finset.sum_sub_distrib]; abel
    rw [this]
    exact Lb.sub_mem (hz j) (Lb.sum_mem fun i _ => hLb _ (hc'O j i) _ (heLb i))
  let n : V ≃ₗ[E] V := LinearEquiv.ofLinearMap (shear h e t) (shear h e (fun j => - t j))
    (by
      ext v
      have := shear_inv h e (fun j => - t j) hntE v
      simpa using this)
    (by ext v; exact shear_inv h e t htE v)
  have hn : ∀ v, n v = v + ∑ j, h v (e j) • t j := fun v => rfl
  refine ⟨n, fun v w => ?_, fun v hv => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [hn, hn]
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
    have h3 : ∀ j k, h (t j) (t k) = 0 := fun j k => by
      simp only [ht]; exact tt _ _
    simp only [h3, mul_zero, Finset.sum_const_zero, add_zero]
    simp only [ht, Et, tv, Finset.mul_sum]
    rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    linear_combination (h v (e i) * star (h w (e j))) * hskew i j
  · rw [hn]; simp [hv]
  · rw [hn]
    have h0 : ∀ i, h (v - ∑ j, h v (e j) • y j) (e i) = 0 := by
      intro i
      simp [map_sum, LinearMap.sum_apply, hd]
    have hm : v - ∑ j, h v (e j) • y j ∈ La :=
      La.sub_mem hv (La.sum_mem fun j _ => hLa _ (hIa _ hv _ (heLa j)) _ (hy j))
    have : v + ∑ j, h v (e j) • t j = (v - ∑ j, h v (e j) • y j) + ∑ j, h v (e j) • (y j + t j) := by
      simp only [smul_add, Finset.sum_add_distrib]; abel
    rw [this]
    exact Lb.add_mem ((hcap _ h0).1 hm) (Lb.sum_mem fun j _ => hLb _ (hIa _ hv _ (heLa j)) _ (hzz j))
  · have hp : ∀ i, h (n v) (e i) = h v (e i) := fun i => shear_pair h e t htE v i
    have hpO : ∀ i, h v (e i) ∈ O := fun i => by rw [← hp]; exact hIb _ hv _ (heLb i)
    have h0 : ∀ i, h (n v - ∑ j, h v (e j) • (y j + t j)) (e i) = 0 := by
      intro i
      simp [map_sum, LinearMap.sum_apply, hd, hp, htE]
    have hm : n v - ∑ j, h v (e j) • (y j + t j) ∈ Lb :=
      Lb.sub_mem hv (Lb.sum_mem fun j _ => hLb _ (hpO j) _ (hzz j))
    have : v = (n v - ∑ j, h v (e j) • (y j + t j)) + ∑ j, h v (e j) • y j := by
      rw [hn]; simp only [smul_add, Finset.sum_add_distrib]; abel
    rw [this]
    exact La.add_mem ((hcap _ h0).2 hm) (La.sum_mem fun j _ => hLa _ (hpO j) _ (hy j))
end Formalism.HermitianLatticeCounting.P.S4aux
