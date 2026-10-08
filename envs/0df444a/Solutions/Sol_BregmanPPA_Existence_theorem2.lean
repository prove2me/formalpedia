-- Prove2me | solution 1 for BregmanPPA.Existence.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T15:40:23.136023+00:00
-- url     : https://prove2.me/submissions/e4b4e094-a194-4be2-9c65-eb3ff4845815

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_Existence_LProperty
set_option autoImplicit false
section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Transport the original extended-real subgradient inequality only at verified finite points. -/
theorem subgradient_real_comparison (f : H → EReal) (hproper : IsProperFn f)
    {u v g : H} (hu : IsSubgradient f u g) (hv : f v ≠ ⊤) :
    (f u).toReal+inner ℝ g (v-u) ≤ (f v).toReal := by
  have heu := EReal.coe_toReal hu.1 (hproper.1 u)
  have hev := EReal.coe_toReal hv (hproper.1 v)
  have hg := hu.2 v
  rw [← heu,← hev,← EReal.coe_add] at hg
  exact EReal.coe_le_coe_iff.mp hg

theorem zero_subgradient_real_min (f : H → EReal) (hproper : IsProperFn f)
    {z v : H} (hz : IsSubgradient f z 0) (hv : f v ≠ ⊤) :
    (f z).toReal ≤ (f v).toReal := by
  simpa using subgradient_real_comparison f hproper hz hv

theorem zero_subgradient_of_min (f : H → EReal) {p : H} (hp : f p ≠ ⊤)
    (hmin : ∀ v : H, f p ≤ f v) : IsSubgradient f p 0 := by
  exact ⟨hp,fun v => by simpa using hmin v⟩

/-- Lower semicontinuity passes a verified objective-value limit to a boundary point. -/
theorem lsc_objective_limit (f : H → EReal) (hf : LowerSemicontinuous f)
    (x : ℕ → H) (p : H) (m : EReal) (hx : Tendsto x atTop (𝓝 p))
    (hm : Tendsto (fun k => f (x k)) atTop (𝓝 m)) : f p ≤ m := by
  by_contra hn
  have hmp : m < f p := lt_of_not_ge hn
  obtain ⟨a,hma,hap⟩ := exists_between hmp
  have hl : ∀ᶠ k in atTop, a < f (x k) := hx.eventually (hf p a hap)
  have hu : ∀ᶠ k in atTop, f (x k) < a := hm.eventually (Iio_mem_nhds hma)
  obtain ⟨k,hk⟩ := (hl.and hu).exists
  exact lt_asymm hk.1 hk.2
end BregmanPPACodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR InertialFB.IFB
namespace BregmanExistenceCodex
open BregmanPPA.Existence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem trimonotone_monotone (R : H → Set H) (hR : IsTrimonotone R) :
    IsMonotoneOp R := by
  intro x z y w hy hw
  have hc := hR x z x y w y hy hw hy
  simp only [sub_self, inner_zero_left, add_zero] at hc
  simp only [inner_sub_left] at hc
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem trimonotone_lproperty (R : H → Set H) (hR : IsTrimonotone R) :
    HasLProperty R := by
  refine ⟨trimonotone_monotone R hR, ?_⟩
  intro u hu v hv
  obtain ⟨a, ha⟩ := hu
  obtain ⟨q, hq⟩ := hv
  refine ⟨inner ℝ (q-u) a + inner ℝ (u-q) v, ?_⟩
  intro t ht
  obtain ⟨x,y,hy,rfl⟩ := ht
  have hc := hR x u q y a v hy ha hq
  simp only [inner_sub_left, inner_sub_right] at hc ⊢
  linarith

theorem subdiff_trimonotone (f : H → EReal) (hp : IsProperFn f) :
    IsTrimonotone (BregmanPPA.Convergence.subdiffOp f) := by
  intro x₀ x₁ x₂ y₀ y₁ y₂ h₀ h₁ h₂
  have h01 := BregmanPPACodex.subgradient_real_comparison f hp h₀ h₁.1
  have h12 := BregmanPPACodex.subgradient_real_comparison f hp h₁ h₂.1
  have h20 := BregmanPPACodex.subgradient_real_comparison f hp h₂ h₀.1
  rw [real_inner_comm] at h01 h12 h20
  linarith
end BregmanExistenceCodex

end

set_option autoImplicit false
open BregmanPPA.Existence InertialFB.IFB

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] :
    (∀ R : H → Set H, IsTrimonotone R → HasLProperty R) ∧
    (∀ f : H → EReal, IsProperFn f → IsConvexFn f →
      HasLProperty (BregmanPPA.Convergence.subdiffOp f)) := by
  exact ⟨BregmanExistenceCodex.trimonotone_lproperty,
    fun f hp _ => BregmanExistenceCodex.trimonotone_lproperty _
      (BregmanExistenceCodex.subdiff_trimonotone f hp)⟩

#print axioms solution
