-- Prove2me | solution 1 for Erdos624.supported_loss_rank_identity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:17:42.967006+00:00
-- url     : https://prove2.me/submissions/497552a2-9529-45b5-85d5-950f26109002

import Mathlib
open Finset

namespace E624R15T
open Finset Module

theorem root {U : Type*} [DecidableEq U] (H P : Finset U) (hHP : H ⊆ P)
    (F : Finset (Finset U)) (hF : ∀ A ∈ F, A ⊆ P) (R : U → Finset U)
    (hR : ∀ x ∈ P \ H, R x ∈ F ∧ x ∈ R x ∧ R x ⊆ insert x H) :
    finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun y => if y ∈ A then (1 : ZMod 2) else 0}) + #H =
      #P + finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun h => if h ∈ H then
          ((if h ∈ A then (1 : ZMod 2) else 0) +
            ∑ x ∈ P \ H, (if x ∈ A then (1 : ZMod 2) else 0) * (if h ∈ R x then 1 else 0))
          else 0}) := by
  classical
  set chi : Finset U → U → ZMod 2 := fun A y => if y ∈ A then 1 else 0 with hchi
  set K := Submodule.span (ZMod 2) {g | ∃ A ∈ F, g = fun y => if y ∈ A then (1 : ZMod 2) else 0}
    with hK
  let Φ : (U → ZMod 2) →ₗ[ZMod 2] (U → ZMod 2) :=
    { toFun := fun f h => if h ∈ H then
          (f h + ∑ x ∈ P \ H, f x * (if h ∈ R x then (1 : ZMod 2) else 0)) else 0
      map_add' := by
        intro f g; ext h; simp only [Pi.add_apply]
        split_ifs
        · simp only [add_mul, sum_add_distrib]; ring
        · simp
      map_smul' := by
        intro c f; ext h; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs
        · simp only [mul_add, mul_sum, mul_assoc]
        · simp }
  have hΦ : ∀ f h, Φ f h = if h ∈ H then
      (f h + ∑ x ∈ P \ H, f x * (if h ∈ R x then (1 : ZMod 2) else 0)) else 0 := fun _ _ => rfl
  -- basic facts about repairs
  have hRP : ∀ x ∈ P \ H, R x ⊆ P := fun x hx =>
    (hR x hx).2.2.trans (insert_subset (mem_sdiff.1 hx).1 hHP)
  have hRx : ∀ x ∈ P \ H, ∀ y ∈ P \ H, (y ∈ R x ↔ y = x) := by
    intro x hx y hy
    constructor
    · intro h
      have := (hR x hx).2.2 h
      rw [mem_insert] at this
      rcases this with h | h
      · exact h
      · exact absurd h (mem_sdiff.1 hy).2
    · intro h; rw [h]; exact (hR x hx).2.1
  have hΦR : ∀ x ∈ P \ H, Φ (chi (R x)) = 0 := by
    intro x hx; ext h
    rw [hΦ]
    split_ifs with hh
    · rw [sum_eq_single x]
      · simp only [hchi, if_pos (hR x hx).2.1, one_mul]
        simp only [Pi.zero_apply]
        split_ifs <;> decide
      · intro y hy hyx
        simp only [hchi, if_neg (fun h => hyx ((hRx x hx y hy).1 h)), zero_mul]
      · intro h; exact absurd hx h
    · rfl
  -- support in P
  let SP : Submodule (ZMod 2) (U → ZMod 2) :=
    { carrier := {f | ∀ y, y ∉ P → f y = 0}
      add_mem' := by intro a b ha hb y hy; simp [ha y hy, hb y hy]
      zero_mem' := by intro y _; rfl
      smul_mem' := by intro c a ha y hy; simp [ha y hy] }
  have hKSP : K ≤ SP := by
    rw [hK, Submodule.span_le]
    rintro g ⟨A, hA, rfl⟩ y hy
    simp only [if_neg (fun h => hy (hF A hA h))]
  -- the repair span
  set Rsp := Submodule.span (ZMod 2) (Set.range (fun x : ↥(P \ H) => chi (R x)))
    with hRsp
  have hRspK : Rsp ≤ K := by
    rw [hRsp, Submodule.span_le]
    rintro g ⟨x, rfl⟩
    exact Submodule.subset_span ⟨R x, (hR x x.2).1, rfl⟩
  have hker : ∀ f ∈ K, Φ f = 0 ↔ f ∈ Rsp := by
    intro f hf
    constructor
    · intro h0
      have hsupp := hKSP hf
      have hrep : f = ∑ x ∈ (P \ H).attach, f x • chi (R x) := by
        ext y
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hyP : y ∈ P
        · by_cases hyH : y ∈ H
          · have := congrFun h0 y
            rw [hΦ, if_pos hyH] at this
            have e : f y = ∑ x ∈ P \ H, f x * (if y ∈ R x then (1 : ZMod 2) else 0) := by
              have := congrArg (fun t => t + ∑ x ∈ P \ H, f x * (if y ∈ R x then (1 : ZMod 2) else 0)) this
              simp only [Pi.zero_apply, zero_add] at this
              rw [← this, add_assoc, ZModModule.add_self, add_zero]
            rw [e, ← sum_attach (P \ H) (fun x => f x * (if y ∈ R x then (1 : ZMod 2) else 0))]
          · have hy : y ∈ P \ H := mem_sdiff.2 ⟨hyP, hyH⟩
            rw [sum_eq_single ⟨y, hy⟩]
            · simp [hchi, (hR y hy).2.1]
            · intro x _ hxy
              have : y ∉ R x := fun h => hxy (Subtype.ext ((hRx x x.2 y hy).1 h).symm)
              simp [hchi, this]
            · intro h; exact absurd (mem_attach _ _) h
        · rw [hsupp y hyP]
          symm; apply sum_eq_zero
          intro x _
          have : y ∉ R x := fun h => hyP (hRP x x.2 h)
          simp [hchi, this]
      rw [hrep]
      exact Rsp.sum_mem fun x _ => Rsp.smul_mem _ (Submodule.subset_span ⟨x, rfl⟩)
    · intro h
      have : Rsp ≤ LinearMap.ker Φ := by
        rw [hRsp, Submodule.span_le]
        rintro g ⟨x, rfl⟩
        exact hΦR x x.2
      exact this h
  -- linear independence of repairs
  have hli : LinearIndependent (ZMod 2) (fun x : ↥(P \ H) => chi (R x)) := by
    rw [linearIndependent_iff']
    intro s g hg x hx
    have := congrFun hg x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [sum_eq_single x] at this
    · simpa [hchi, (hR x x.2).2.1] using this
    · intro y _ hyx
      have : (x : U) ∉ R y := fun h => hyx (Subtype.ext ((hRx y y.2 x x.2).1 h).symm)
      simp [hchi, this]
    · intro h; exact absurd hx h
  have hRdim : finrank (ZMod 2) Rsp = #(P \ H) := by
    rw [hRsp, finrank_span_eq_card hli, Fintype.card_coe]
  -- finite dimensionality
  have hfin : (({g | ∃ A ∈ F, g = fun y => if y ∈ A then (1 : ZMod 2) else 0}) :
      Set (U → ZMod 2)).Finite := by
    refine ((F.finite_toSet).image chi).subset ?_
    rintro g ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩
  have : FiniteDimensional (ZMod 2) K := FiniteDimensional.span_of_finite _ hfin
  -- rank–nullity
  have hrn := LinearMap.finrank_range_add_finrank_ker (Φ.domRestrict K)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
  have hk2 : (LinearMap.ker Φ).comap K.subtype = Rsp.comap K.subtype := by
    ext ⟨v, hv⟩
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker]
    exact hker v hv
  rw [hk2, (Submodule.comapSubtypeEquivOfLe hRspK).finrank_eq, hRdim] at hrn
  have hmap : Submodule.map Φ K = Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun h => if h ∈ H then
          ((if h ∈ A then (1 : ZMod 2) else 0) +
            ∑ x ∈ P \ H, (if x ∈ A then (1 : ZMod 2) else 0) * (if h ∈ R x then 1 else 0))
          else 0} := by
    rw [hK, Submodule.map_span]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩; exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  rw [hmap] at hrn
  rw [card_sdiff_of_subset hHP] at hrn
  have := card_le_card hHP
  omega
end E624R15T

namespace Erdos624

theorem supported_loss_rank_identity {U : Type*} [DecidableEq U] (H P : Finset U) (hHP : H ⊆ P)
    (F : Finset (Finset U)) (hF : ∀ A ∈ F, A ⊆ P) (R : U → Finset U)
    (hR : ∀ x ∈ P \ H, R x ∈ F ∧ x ∈ R x ∧ R x ⊆ insert x H) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun y => if y ∈ A then (1 : ZMod 2) else 0}) + #H =
      #P + Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun h => if h ∈ H then
          ((if h ∈ A then (1 : ZMod 2) else 0) +
            ∑ x ∈ P \ H, (if x ∈ A then (1 : ZMod 2) else 0) * (if h ∈ R x then 1 else 0))
          else 0}) := by
  exact E624R15T.root H P hHP F hF R hR

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] (H P : Finset U) (hHP : H ⊆ P)
    (F : Finset (Finset U)) (hF : ∀ A ∈ F, A ⊆ P) (R : U → Finset U)
    (hR : ∀ x ∈ P \ H, R x ∈ F ∧ x ∈ R x ∧ R x ⊆ insert x H) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun y => if y ∈ A then (1 : ZMod 2) else 0}) + #H =
      #P + Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun h => if h ∈ H then
          ((if h ∈ A then (1 : ZMod 2) else 0) +
            ∑ x ∈ P \ H, (if x ∈ A then (1 : ZMod 2) else 0) * (if h ∈ R x then 1 else 0))
          else 0}) :=
  Erdos624.supported_loss_rank_identity H P hHP F hF R hR
