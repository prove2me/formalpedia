-- Prove2me | solution 1 for DetDLP.m89_s1_winning_seed_mean
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T20:25:44.896318+00:00
-- url     : https://prove2.me/submissions/584c6eb8-4c4f-4526-a670-662f48d260fa

import Theorems.Thm_DetDLP_m89_prefix_descent_mean
import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem packed_injective {m t b : ℕ} {u v : Fin m → Fin t → ℕ}
    (hu : ∀ i j, u i j < 2^b) (hv : ∀ i j, v i j < 2^b)
    (heq : packBits (b := b) u = packBits (b := b) v) : u = v := by
  funext i j
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < b
  · have h := congrFun heq (finProdFinEquiv (finProdFinEquiv (i,j), (⟨k, hk⟩ : Fin b).rev))
    simpa [packBits] using h
  · have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hk)
    rw [Nat.testBit_lt_two_pow ((hu i j).trans_le hb),
      Nat.testBit_lt_two_pow ((hv i j).trans_le hb)]

private theorem pair_bounds {p : ℕ} (ab : Fin (p-1) × Fin p) :
    ab.1.val + 1 < p ∧ ab.2.val < p := by
  have h := ab.1.isLt
  exact ⟨by omega, ab.2.isLt⟩

private theorem fp_pack_inj (p m : ℕ) : Function.Injective (@fpBits p m) := by
  intro a b h
  have bounded (s : FpSeed p m) (i k) : fpWords s i k < 2^(bitLen p) := by
    apply Nat.lt_of_lt_of_le _ (Nat.le_pow_clog (by decide : 1 < 2) p)
    unfold fpWords
    split
    · exact (pair_bounds _).1
    · exact (pair_bounds _).2
  have hw := packed_injective (bounded a) (bounded b) h
  funext i
  apply Prod.ext <;> apply Fin.ext
  · have hh := congrFun (congrFun hw i) (0 : Fin 2)
    change (a i).1.val + 1 = (b i).1.val + 1 at hh
    omega
  · exact congrFun (congrFun hw i) (1 : Fin 2)

private theorem ec_pack_inj (p m : ℕ) : Function.Injective (@ecBits p m) := by
  intro a b h
  have bounded (s : ECSeed p m) (i k) : ecWords s i k < 2^(bitLen p) := by
    apply Nat.lt_of_lt_of_le _ (Nat.le_pow_clog (by decide : 1 < 2) p)
    unfold ecWords
    dsimp only
    split
    · exact (pair_bounds _).1
    · exact (pair_bounds _).2
  have hw := packed_injective (bounded a) (bounded b) h
  funext i v
  cases v
  · apply Prod.ext <;> apply Fin.ext
    · have hh := congrFun (congrFun hw i) (0 : Fin 4)
      change (a i false).1.val + 1 = (b i false).1.val + 1 at hh
      omega
    · exact congrFun (congrFun hw i) (1 : Fin 4)
  · apply Prod.ext <;> apply Fin.ext
    · have hh := congrFun (congrFun hw i) (2 : Fin 4)
      change (a i true).1.val + 1 = (b i true).1.val + 1 at hh
      omega
    · exact congrFun (congrFun hw i) (3 : Fin 4)

private theorem winning_bound {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool)
    (inj : Function.Injective bits) (f : α → ℝ) (s : α) (hs : s ∈ winners bits f) :
    f s ≤ (∑ x, f x) / (Fintype.card α : ℝ) := by
  classical
  let good (k : ℕ) (a : Node α) : Prop := a.1 + k = L ∧
    ∀ x ∈ a.2, ∀ y ∈ a.2, ∀ j : Fin L, j.val < a.1 → bits x j = bits y j
  let cnt (a : Node α) := a.2.card
  let cost (a : Node α) := ∑ x ∈ a.2, f x
  let root : Node α := (0,Finset.univ)
  have hz (a : Node α) (ha : cnt a = 0) : cost a = 0 := by
    have h : a.2 = ∅ := Finset.card_eq_zero.mp ha
    simp [cost, h]
  have split_node (k : ℕ) (a : Node α) (ha : good (k+1) a) :
      cnt a = cnt (child bits a false) + cnt (child bits a true) ∧
      cost a = cost (child bits a false) + cost (child bits a true) ∧
      ∀ v, good k (child bits a v) := by
    obtain ⟨hlen, heq⟩ := ha
    have hj : a.1 < L := by omega
    let idx : Fin L := ⟨a.1,hj⟩
    constructor
    · simpa [cnt, child, hj, idx] using
        (Finset.card_filter_add_card_filter_not (s := a.2) (fun x => bits x idx = false)).symm
    constructor
    · simpa [cost, child, hj, idx] using
        (Finset.sum_filter_add_sum_filter_not a.2 (fun x => bits x idx = false) f).symm
    · intro v
      refine ⟨by change a.1+1+k = L; omega, ?_⟩
      intro x hx y hy j hj'
      simp only [child, dif_pos hj, Finset.mem_filter] at hx hy
      change j.val < a.1+1 at hj'
      by_cases he : j.val < a.1
      · exact heq x hx.1 y hy.1 j he
      · have hji : j = idx := Fin.ext (by change j.val = a.1; omega)
        subst j
        exact hx.2.trans hy.2.symm
  have hr : good L root := ⟨by simp [root], by simp [root]⟩
  have hp : 0 < cnt root := Finset.card_pos.mpr ⟨s, Finset.mem_univ _⟩
  let z := M89SeedSelection.descend cnt cost (child bits) L root
  obtain ⟨(hg : good 0 z), _, (hmean : cost z / cnt z ≤ cost root / cnt root)⟩ :=
    m89_prefix_descent_mean cnt cost (child bits) hz good split_node L root hr hp
  change s ∈ z.2 at hs
  have hsingleton : z.2 = {s} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hs, ?_⟩
    intro x hx
    apply inj
    funext j
    exact hg.2 x hx s hs j (by have := hg.1; have := j.isLt; omega)
  simpa [cost, cnt, hsingleton, root] using hmean

theorem solution :
    (∀ (p m : ℕ) [Fact p.Prime] (S : FpSeed p m),
      S ∈ winners fpBits (fpCost p m) →
      fpCost p m S ≤ (∑ s : FpSeed p m, fpCost p m s) / (Fintype.card (FpSeed p m) : ℝ)) ∧
    (∀ (p m : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m),
      S ∈ winners ecBits (ecCost E (m := m)) →
      ecCost E S ≤ (∑ s : ECSeed p m, ecCost E s) / (Fintype.card (ECSeed p m) : ℝ)) := by
  constructor
  · intro p m inst S hS
    exact winning_bound fpBits (fp_pack_inj p m) (fpCost p m) S hS
  · intro p m inst E S hS
    exact winning_bound ecBits (ec_pack_inj p m) (ecCost E) S hS
