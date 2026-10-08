-- Prove2me | solution 1 for ConvexRiskFn.Cont.continuousOn_of_lsc_interior
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:06:38.327659+00:00
-- url     : https://prove2.me/submissions/dd19fa59-893a-4b2e-adcd-49e1a38cd4fd

import Definitions.Def_ConvexRiskFn_Cont_Setting
set_option autoImplicit false
open Filter Topology Set

private theorem convex_lsc_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C : Set E} {f : E → ℝ}
    (hC : IsOpen C) (hf : ConvexOn ℝ C f) (hlsc : LowerSemicontinuousOn f C) :
    ContinuousOn f C := by
  classical
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let : BaireSpace C := hC.baireSpace
    let s : ℕ → Set C := fun n => {x | f x ≤ (n : ℝ)}
    have hc : ∀ n, IsClosed (s n) := fun n =>
      (lowerSemicontinuous_restrict_iff.mpr hlsc).isClosed_preimage (n:ℝ)
    have hcover : ⋃ n, s n = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨n,hn⟩ := exists_nat_gt (f x)
      exact mem_iUnion.mpr ⟨n,hn.le⟩
    obtain ⟨n,y,hy⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
    let V : Set E := Subtype.val '' interior (s n)
    have ho : IsOpen V := hC.isOpenMap_subtype_val _ isOpen_interior
    have hyV : (y:E) ∈ V := mem_image_of_mem _ hy
    have hb : ∀ z ∈ V, f z ≤ (n:ℝ) := by
      rintro z ⟨w,hw,rfl⟩
      exact (show w ∈ s n from interior_subset hw)
    apply ((hf.continuousOn_tfae hC hne).out 3 1).mp
    refine ⟨y,y.property,(n:ℝ),?_⟩
    exact (ho.eventually_mem hyV).mono (fun z hz => hb z hz)
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ : E → EReal) (hρ : ConvexRiskFn.Cont.IsProper ρ)
    (h1 : ConvexRiskFn.Dual.A1 ρ)
    (hlsc : ∀ X ∈ interior (ConvexRiskFn.Dual.dom ρ), LowerSemicontinuousAt ρ X) :
    ContinuousOn ρ (interior (ConvexRiskFn.Dual.dom ρ)) := by
  let C := ConvexRiskFn.Dual.dom ρ
  let f := fun x => (ρ x).toReal
  have hfinite (x:E) (hx:x∈C) : (f x : EReal)=ρ x :=
    EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (hρ.1 x))
  have hconv : ConvexOn ℝ C f := by
    have hd : Convex ℝ C := by
      intro x hx y hy a b ha hb hab
      have ha1 : a ≤ 1 := by linarith
      have h := h1 x y a ha ha1
      have hb' : 1-a=b := by linarith
      rw [hb',← hfinite x hx,← hfinite y hy,← EReal.coe_mul,← EReal.coe_mul,
        ← EReal.coe_add] at h
      exact lt_of_le_of_lt h (EReal.coe_lt_top _)
    refine ⟨hd,?_⟩
    intro x hx y hy a b ha hb hab
    have h := h1 x y a ha (by linarith)
    have hb' : 1-a=b := by linarith
    rw [hb',← hfinite x hx,← hfinite y hy,← hfinite _ (hd hx hy ha hb hab),
      ← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,EReal.coe_le_coe_iff] at h
    exact h
  have hlow : LowerSemicontinuousOn f (interior C) := by
    intro x hx
    apply LowerSemicontinuousAt.lowerSemicontinuousWithinAt
    rw [lowerSemicontinuousAt_iff]
    intro b hb
    have he : (b:EReal)<ρ x := by
      rw [← hfinite x (interior_subset hx),EReal.coe_lt_coe_iff]
      exact hb
    have h := (lowerSemicontinuousAt_iff.mp (hlsc x hx)) (b:EReal) he
    filter_upwards [h,isOpen_interior.eventually_mem hx] with y hy hyC
    rwa [← hfinite y (interior_subset hyC),EReal.coe_lt_coe_iff] at hy
  have hc := convex_lsc_continuous isOpen_interior (hconv.subset interior_subset hconv.1.interior) hlow
  have hco : ContinuousOn (fun x => (f x:EReal)) (interior C) :=
    continuous_coe_real_ereal.comp_continuousOn hc
  exact hco.congr (fun x hx => (hfinite x (interior_subset hx)).symm)

#print axioms solution

open ConvexRiskFn.Cont Filter Topology
namespace ConvexRiskFn.Cont

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ)
    (hlsc : ∀ X ∈ interior (ConvexRiskFn.Dual.dom ρ), LowerSemicontinuousAt ρ X) :
    ContinuousOn ρ (interior (ConvexRiskFn.Dual.dom ρ)) := by
  exact solution ρ hρ h1 hlsc

end ConvexRiskFn.Cont

#print axioms solution
