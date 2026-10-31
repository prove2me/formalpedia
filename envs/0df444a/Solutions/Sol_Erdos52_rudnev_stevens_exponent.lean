-- Prove2me | solution 1 for Erdos52.rudnev_stevens_exponent
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T13:47:42.908704+00:00
-- url     : https://prove2.me/submissions/b1aa6d7c-0ed9-4b22-96bc-3d7f58e8b871

import Mathlib
open scoped Pointwise

-- BEGIN RSProof/SharedBasics.lean

open scoped BigOperators Pointwise

namespace Erdos52.RSFresh

noncomputable def diffCount (A B : Finset ℝ) (t : ℝ) : ℕ := by
  classical
  exact ((A ×ˢ B).filter (fun p => p.1-p.2=t)).card
noncomputable def sumCount (A B : Finset ℝ) (t : ℝ) : ℕ := by
  classical
  exact ((A ×ˢ B).filter (fun p => p.1+p.2=t)).card
noncomputable def ratioCount (A B : Finset ℝ) (t : ℝ) : ℕ := by
  classical
  exact ((A ×ˢ B).filter (fun p => p.1/p.2=t)).card
noncomputable def energy2 (A B : Finset ℝ) : ℕ := by
  classical
  exact ∑ t ∈ A-B, (diffCount A B t)^2
noncomputable def addEnergy (A : Finset ℝ) : ℕ := energy2 A A
noncomputable def mulEnergy (A : Finset ℝ) : ℕ := by
  classical
  exact ∑ t ∈ A/A, (ratioCount A A t)^2

def Positive (A : Finset ℝ) : Prop := ∀ x ∈ A, 0 < x

def logBudget (n : ℕ) : ℕ := Nat.log 2 n + 4

end Erdos52.RSFresh

-- END RSProof/SharedBasics.lean

-- BEGIN RSProof/SlopeGeometry.lean

open scoped Pointwise
namespace Erdos52.RSFresh

def slopeMix (lam μ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1+p.2, lam*p.1+μ*p.2)

theorem slopeMix_injective (lam μ : ℝ) (h : lam ≠ μ) :
    Function.Injective (slopeMix lam μ) := by
  intro p q he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change p.1+p.2=q.1+q.2 at hx
  change lam*p.1+μ*p.2=lam*q.1+μ*q.2 at hy
  have hd : (lam-μ)*(p.1-q.1)=0 := by
    linear_combination hy - μ * hx
  have hp : p.1=q.1 := by
    have hz := (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr h)
    linarith
  exact Prod.ext hp (by linarith)

theorem slopeMix_between (lam μ x y : ℝ) (hlamμ : lam < μ) (hx : 0 < x) (hy : 0 < y) :
    lam < (slopeMix lam μ (x,y)).2 / (slopeMix lam μ (x,y)).1 ∧
    (slopeMix lam μ (x,y)).2 / (slopeMix lam μ (x,y)).1 < μ := by
  change lam < (lam*x+μ*y)/(x+y) ∧ (lam*x+μ*y)/(x+y) < μ
  have hp : 0 < x+y := by positivity
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith
  · apply (div_lt_iff₀ hp).mpr
    nlinarith

noncomputable def slopeFiber (A : Finset ℝ) (lam : ℝ) : Finset ℝ := by
  classical
  exact A.filter (fun x => lam*x ∈ A)

noncomputable def slopeSums (A : Finset ℝ) (lam μ : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact ((slopeFiber A lam) ×ˢ (slopeFiber A μ)).image (slopeMix lam μ)

theorem slopeSums_card (A : Finset ℝ) (lam μ : ℝ) (h : lam ≠ μ) :
    (slopeSums A lam μ).card = (slopeFiber A lam).card * (slopeFiber A μ).card := by
  classical
  rw [slopeSums, Finset.card_image_of_injective _ (slopeMix_injective lam μ h),
    Finset.card_product]

theorem slopeSums_subset (A : Finset ℝ) (lam μ : ℝ) :
    slopeSums A lam μ ⊆ (A+A) ×ˢ (A+A) := by
  classical
  intro p hp
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  obtain ⟨hxA,hlamx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyA,hμy⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_product.mpr ⟨Finset.add_mem_add hxA hyA,
    Finset.add_mem_add hlamx hμy⟩

theorem slopeSums_ratio (A : Finset ℝ) (hA : Positive A) (lam μ : ℝ)
    (hlamμ : lam < μ) {p : ℝ × ℝ} (hp : p ∈ slopeSums A lam μ) :
    lam < p.2/p.1 ∧ p.2/p.1 < μ := by
  classical
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  exact slopeMix_between lam μ x y hlamμ
    (hA x (Finset.mem_filter.mp hx).1) (hA y (Finset.mem_filter.mp hy).1)

theorem slopeSums_disjoint (A : Finset ℝ) (hA : Positive A)
    (lam μ ν ξ : ℝ) (hlamμ : lam < μ) (hμν : μ ≤ ν) (hνξ : ν < ξ) :
    Disjoint (slopeSums A lam μ) (slopeSums A ν ξ) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hh := slopeSums_ratio A hA lam μ hlamμ hp
  have hi := slopeSums_ratio A hA ν ξ hνξ hq
  linarith

end Erdos52.RSFresh

-- END RSProof/SlopeGeometry.lean

-- BEGIN RSProof/CountBasics.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem diffCount_le_left (A B : Finset ℝ) (t : ℝ) : diffCount A B t ≤ A.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℝ × ℝ => p.1)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext he
    dsimp at hp' hq' he ⊢
    linarith

 theorem diffCount_le_right (A B : Finset ℝ) (t : ℝ) : diffCount A B t ≤ B.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℝ × ℝ => p.2)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext _ he
    dsimp at hp' hq' he ⊢
    linarith

 theorem sum_diffCount (A B : Finset ℝ) : ∑ t ∈ A-B, diffCount A B t = A.card*B.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := A ×ˢ B) (t := A-B)
    (f := fun p : ℝ × ℝ => p.1-p.2) (by
      intro p hp
      exact Finset.sub_mem_sub (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  simpa only [Finset.card_product, diffCount] using h.symm

 theorem sum_sumCount (A B : Finset ℝ) : ∑ t ∈ A+B, sumCount A B t = A.card*B.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := A ×ˢ B) (t := A+B)
    (f := fun p : ℝ × ℝ => p.1+p.2) (by
      intro p hp
      exact Finset.add_mem_add (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  simpa only [Finset.card_product, sumCount] using h.symm

 theorem sum_ratioCount (A B : Finset ℝ) : ∑ t ∈ A/B, ratioCount A B t = A.card*B.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := A ×ˢ B) (t := A/B)
    (f := fun p : ℝ × ℝ => p.1/p.2) (by
      intro p hp
      exact Finset.div_mem_div (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  simpa only [Finset.card_product, ratioCount] using h.symm

 theorem energy2_lower (A B : Finset ℝ) : A.card*B.card ≤ energy2 A B := by
  classical
  rw [← sum_diffCount]
  apply Finset.sum_le_sum
  intro t ht
  have h : diffCount A B t = 0 ∨ 1 ≤ diffCount A B t := by omega
  rcases h with h | h
  · simp [h]
  · nlinarith

 theorem energy2_upper (A B : Finset ℝ) : energy2 A B ≤ A.card^2*B.card := by
  classical
  calc
    energy2 A B ≤ ∑ t ∈ A-B, A.card*diffCount A B t := by
      apply Finset.sum_le_sum
      intro t ht
      have h := diffCount_le_left A B t
      nlinarith
    _ = A.card*(A.card*B.card) := by rw [← Finset.mul_sum, sum_diffCount]
    _ = A.card^2*B.card := by ring

 theorem addEnergy_lower (A : Finset ℝ) : A.card^2 ≤ addEnergy A := by
  simpa only [addEnergy, pow_two] using energy2_lower A A
 theorem addEnergy_upper (A : Finset ℝ) : addEnergy A ≤ A.card^3 := by
  have h := energy2_upper A A
  simpa only [addEnergy, pow_succ] using h

end Erdos52.RSFresh

-- END RSProof/CountBasics.lean

-- BEGIN RSProof/SlopeCounts.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem slopeFiber_card (A : Finset ℝ) (hA : Positive A) (lam : ℝ) :
    (slopeFiber A lam).card = ratioCount A A lam := by
  classical
  have hi : Function.Injective (fun x : ℝ => (lam*x,x)) := by
    intro x y h
    exact congrArg Prod.snd h
  have he : (slopeFiber A lam).image (fun x => (lam*x,x)) =
      (A ×ˢ A).filter (fun p => p.1/p.2=lam) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hx,hlamx⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hlamx,hx⟩, ?_⟩
      exact (div_eq_iff (ne_of_gt (hA x hx))).mpr rfl
    · intro hp
      obtain ⟨hp,hdiv⟩ := Finset.mem_filter.mp hp
      obtain ⟨hy,hx⟩ := Finset.mem_product.mp hp
      have heq : p.1=lam*p.2 := (div_eq_iff (ne_of_gt (hA p.2 hx))).mp hdiv
      apply Finset.mem_image.mpr
      refine ⟨p.2, Finset.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
      · rwa [← heq]
      · exact Prod.ext heq.symm rfl
  rw [← Finset.card_image_of_injective (slopeFiber A lam) hi, he]
  rfl

theorem slopeFiber_card_le (A : Finset ℝ) (lam : ℝ) :
    (slopeFiber A lam).card ≤ A.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem sum_slopeFiber (A : Finset ℝ) (hA : Positive A) :
    ∑ lam ∈ A/A, (slopeFiber A lam).card = A.card^2 := by
  simp_rw [slopeFiber_card A hA]
  simpa only [pow_two] using sum_ratioCount A A

theorem mulEnergy_slopeFiber (A : Finset ℝ) (hA : Positive A) :
    mulEnergy A = ∑ lam ∈ A/A, (slopeFiber A lam).card^2 := by
  simp_rw [slopeFiber_card A hA]
  rfl

end Erdos52.RSFresh

-- END RSProof/SlopeCounts.lean

-- BEGIN RSProof/SlopeChain.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem slope_chain_bound (A : Finset ℝ) (hA : Positive A) (m τ : ℕ)
    (lam : ℕ → ℝ)
    (hmono : ∀ i j, i < j → j ≤ m → lam i < lam j)
    (hτ : ∀ i, i ≤ m → τ ≤ (slopeFiber A (lam i)).card) :
    m * τ^2 ≤ (A+A).card^2 := by
  classical
  let F := fun i => slopeSums A (lam i) (lam (i+1))
  have hd : (Finset.range m : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    have hi' : i < m := Finset.mem_range.mp hi
    have hj' : j < m := Finset.mem_range.mp hj
    have hforward (a b : ℕ) (ha : a < m) (hb : b < m) (hab : a < b) :
        Disjoint (F a) (F b) := by
      apply slopeSums_disjoint A hA
      · exact hmono a (a+1) (by omega) (by omega)
      · by_cases he : a+1=b
        · rw [he]
        · exact (hmono (a+1) b (by omega) (by omega)).le
      · exact hmono b (b+1) (by omega) (by omega)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hforward i j hi' hj' h
    · exact (hforward j i hj' hi' h).symm
  have hs : (Finset.range m).disjiUnion F hd ⊆ (A+A) ×ˢ (A+A) := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_disjiUnion.mp hp
    exact slopeSums_subset A (lam i) (lam (i+1)) hp
  calc
    m * τ^2 = ∑ _i ∈ Finset.range m, τ^2 := by simp
    _ ≤ ∑ i ∈ Finset.range m, (F i).card := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      rw [show (F i).card = (slopeFiber A (lam i)).card *
        (slopeFiber A (lam (i+1))).card from
        slopeSums_card A _ _ (ne_of_lt (hmono i (i+1) (by omega) (by omega)))]
      simpa only [pow_two] using Nat.mul_le_mul (hτ i (by omega)) (hτ (i+1) (by omega))
    _ = ((Finset.range m).disjiUnion F hd).card := (Finset.card_disjiUnion _ _ _).symm
    _ ≤ ((A+A) ×ˢ (A+A)).card := Finset.card_le_card hs
    _ = (A+A).card^2 := by rw [Finset.card_product, pow_two]

end Erdos52.RSFresh

-- END RSProof/SlopeChain.lean

-- BEGIN RSProof/SlopeSetBound.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem slope_set_bound (A : Finset ℝ) (hA : Positive A) (S : Finset ℝ) (τ : ℕ)
    (hτ : ∀ lam ∈ S, τ ≤ (slopeFiber A lam).card) :
    (S.card-1)*τ^2 ≤ (A+A).card^2 := by
  classical
  by_cases hS : S.Nonempty
  · let e := S.orderEmbOfFin rfl
    let lam : ℕ → ℝ := fun i => if hi : i < S.card then e ⟨i,hi⟩ else 0
    have he (i : ℕ) (hi : i < S.card) : lam i = e ⟨i,hi⟩ := by
      simp only [lam, dif_pos hi]
    apply slope_chain_bound A hA (S.card-1) τ lam
    · intro i j hij hj
      have hj' : j < S.card := by have := hS.card_pos; omega
      have hi' : i < S.card := by omega
      rw [he i hi', he j hj']
      exact e.strictMono (show (⟨i,hi'⟩ : Fin S.card) < ⟨j,hj'⟩ from hij)
    · intro i hi
      have hi' : i < S.card := by have := hS.card_pos; omega
      rw [he i hi']
      apply hτ
      exact S.orderEmbOfFin_mem rfl ⟨i,hi'⟩
  · have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    simp [hz]

end Erdos52.RSFresh

-- END RSProof/SlopeSetBound.lean

-- BEGIN RSProof/LogBudget.lean

namespace Erdos52.RSFresh

theorem logBudget_pos (n : ℕ) : 0 < logBudget n := by
  unfold logBudget
  omega

theorem logBudget_power (n : ℕ) : 8 * (n : ℝ) ≤ (2 : ℝ) ^ logBudget n := by
  have hn := Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) n
  have hr : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hn.le
  have he : (2 : ℝ) ^ logBudget n = 8 * (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    unfold logBudget
    rw [show Nat.log 2 n + 4 = (Nat.log 2 n + 1) + 3 by omega, pow_add]
    norm_num
    ring
  rw [he]
  linarith

end Erdos52.RSFresh

-- END RSProof/LogBudget.lean

-- BEGIN RSProof/DyadicClasses.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def dyadicClass {α : Type*} (S : Finset α) (f : α → ℕ) (j : ℕ) : Finset α := by
  classical
  exact S.filter (fun x => Nat.log 2 (f x)=j)

theorem dyadicClass_bounds {α : Type*} (S : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ S, 0 < f x) (j : ℕ) {x : α} (hx : x ∈ dyadicClass S f j) :
    2^j ≤ f x ∧ f x < 2*2^j := by
  classical
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hlo := Nat.pow_log_le_self 2 (Nat.ne_of_gt (hf x hx))
  have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) (f x)
  rw [hj] at hlo hhi
  simpa only [pow_succ, Nat.mul_comm] using And.intro hlo hhi

theorem dyadic_square_partition {α : Type*} (S : Finset α) (f : α → ℕ) (n : ℕ)
    (hf : ∀ x ∈ S, f x ≤ n) :
    ∑ j ∈ Finset.range (logBudget n), ∑ x ∈ dyadicClass S f j, (f x)^2 =
      ∑ x ∈ S, (f x)^2 := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro x hx
  apply Finset.mem_range.mpr
  have hh := Nat.log_mono_right (b := 2) (hf x hx)
  unfold logBudget
  omega

theorem dyadic_square_bound {α : Type*} (S : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ S, 0 < f x) (j : ℕ) :
    (∑ x ∈ dyadicClass S f j, (f x)^2) ≤ 4*(dyadicClass S f j).card*(2^j)^2 := by
  classical
  calc
    (∑ x ∈ dyadicClass S f j, (f x)^2) ≤ ∑ _x ∈ dyadicClass S f j, 4*(2^j)^2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hh := (dyadicClass_bounds S f hf j hx).2
      nlinarith
    _ = 4*(dyadicClass S f j).card*(2^j)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      ring

theorem exists_dyadic_square_class {α : Type*} (S : Finset α) (f : α → ℕ) (n : ℕ)
    (hpos : ∀ x ∈ S, 0 < f x) (hbound : ∀ x ∈ S, f x ≤ n) :
    ∃ j < logBudget n,
      (∑ x ∈ S, (f x)^2) ≤ 4*logBudget n*(dyadicClass S f j).card*(2^j)^2 := by
  classical
  let g := fun j => ∑ x ∈ dyadicClass S f j, (f x)^2
  obtain ⟨j,hj,hmax⟩ := (Finset.range (logBudget n)).exists_max_image g
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (logBudget_pos n)))
  refine ⟨j,Finset.mem_range.mp hj,?_⟩
  have hp := dyadic_square_partition S f n hbound
  have hb : (∑ x ∈ S, (f x)^2) ≤ logBudget n * g j := by
    rw [← hp]
    calc
      (∑ i ∈ Finset.range (logBudget n), g i) ≤
          ∑ _i ∈ Finset.range (logBudget n), g j :=
        Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = logBudget n*g j := by simp
  have hh := Nat.mul_le_mul_left (logBudget n) (dyadic_square_bound S f hpos j)
  dsimp only [g] at hb
  nlinarith

end Erdos52.RSFresh

-- END RSProof/DyadicClasses.lean

-- BEGIN RSProof/SolymosiEnergy.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem slopeFiber_pos (A : Finset ℝ) (hA : Positive A) {t : ℝ} (ht : t ∈ A/A) :
    0 < (slopeFiber A t).card := by
  classical
  obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_div.mp ht
  apply Finset.card_pos.mpr
  refine ⟨y,Finset.mem_filter.mpr ⟨hy,?_⟩⟩
  simpa only [div_mul_cancel₀ _ (ne_of_gt (hA y hy))] using hx

theorem card_le_sumset (A : Finset ℝ) : A.card ≤ (A+A).card := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a,ha⟩ := hA
    apply Finset.card_le_card_of_injOn (fun x : ℝ => x+a)
    · intro x hx
      exact Finset.add_mem_add hx ha
    · intro x hx y hy he
      exact add_right_cancel he
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

theorem slope_class_weight (A : Finset ℝ) (hA : Positive A) (S : Finset ℝ) (τ : ℕ)
    (hτ : ∀ t ∈ S, τ ≤ (slopeFiber A t).card) :
    S.card*τ^2 ≤ 2*(A+A).card^2 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨t,ht⟩ := hS
    have hh := slope_set_bound A hA S τ hτ
    have htn := (hτ t ht).trans (slopeFiber_card_le A t)
    have hn := card_le_sumset A
    have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨t,ht⟩
    have he : S.card = (S.card-1)+1 := by omega
    have ht2 : τ^2 ≤ (A+A).card^2 := Nat.pow_le_pow_left (htn.trans hn) 2
    rw [he]
    nlinarith
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

theorem solymosi_energy (A : Finset ℝ) (hA : Positive A) :
    mulEnergy A ≤ 8 * logBudget A.card * (A+A).card^2 := by
  classical
  rw [mulEnergy_slopeFiber A hA,
    ← dyadic_square_partition (A/A) (fun t => (slopeFiber A t).card) A.card
      (fun t _ => slopeFiber_card_le A t)]
  calc
    (∑ j ∈ Finset.range (logBudget A.card),
        ∑ t ∈ dyadicClass (A/A) (fun t => (slopeFiber A t).card) j,
          (slopeFiber A t).card^2) ≤
        ∑ _j ∈ Finset.range (logBudget A.card), 8*(A+A).card^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := dyadic_square_bound (A/A) (fun t => (slopeFiber A t).card)
        (fun _ ht => slopeFiber_pos A hA ht) j
      have hc := slope_class_weight A hA
        (dyadicClass (A/A) (fun t => (slopeFiber A t).card) j) (2^j)
        (fun t ht => (dyadicClass_bounds (A/A) (fun t => (slopeFiber A t).card)
          (fun _ hs => slopeFiber_pos A hA hs) j ht).1)
      nlinarith
    _ = 8 * logBudget A.card * (A+A).card^2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
      ring

end Erdos52.RSFresh

-- END RSProof/SolymosiEnergy.lean

-- BEGIN RSProof/FiberCollision.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem fiber_collision {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ((S ×ˢ S).filter (fun p => f p.1=f p.2)).card =
      ∑ v ∈ S.image f, ((S.filter (fun x => f x=v)).card)^2 := by
  let F : β → Finset (α × α) := fun v => (S.filter (fun x => f x=v)) ×ˢ (S.filter (fun x => f x=v))
  have hd : (↑(S.image f) : Set β).PairwiseDisjoint F := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have h1 := (Finset.mem_filter.mp (Finset.mem_product.mp hpa).1).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_product.mp hpb).1).2
    exact hab (h1.symm.trans h2)
  have he : (S ×ˢ S).filter (fun p => f p.1=f p.2) = (S.image f).disjiUnion F hd := by
    ext p
    simp only [Finset.mem_disjiUnion, F, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro hp
      exact ⟨f p.1, Finset.mem_image_of_mem f hp.1.1, ⟨⟨hp.1.1,rfl⟩,⟨hp.1.2,hp.2.symm⟩⟩⟩
    · rintro ⟨v, hv, ⟨hx,hfx⟩, ⟨hy,hfy⟩⟩
      exact ⟨⟨hx,hy⟩,hfx.trans hfy.symm⟩
  rw [he, Finset.card_disjiUnion]
  simp only [F, Finset.card_product, sq]

 theorem energy2_eq_collision (A B : Finset ℝ) :
    energy2 A B = (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter
      (fun p => p.1.1-p.1.2 = p.2.1-p.2.2)).card := by
  classical
  have hi : (A ×ˢ B).image (fun p : ℝ × ℝ => p.1-p.2) = A-B := by
    ext t
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_sub, Prod.exists]
    aesop
  rw [fiber_collision (A ×ˢ B) (fun p : ℝ × ℝ => p.1-p.2), hi]
  rfl

end Erdos52.RSFresh

-- END RSProof/FiberCollision.lean

-- BEGIN RSProof/MixedFiber.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem mixed_fiber_collision {α β κ : Type*} [DecidableEq κ]
    (S : Finset α) (T : Finset β) (U : Finset κ) (f : α → κ) (g : β → κ)
    (hf : ∀ x ∈ S, f x ∈ U) :
    ((S ×ˢ T).filter (fun p => f p.1=g p.2)).card =
      ∑ v ∈ U, (S.filter (fun x => f x=v)).card*(T.filter (fun y => g y=v)).card := by
  classical
  let F := fun v => (S.filter (fun x => f x=v)) ×ˢ (T.filter (fun y => g y=v))
  have hd : (U : Set κ).PairwiseDisjoint F := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have hq' := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
    exact hab (hp'.symm.trans hq')
  have he : (S ×ˢ T).filter (fun p => f p.1=g p.2) = U.disjiUnion F hd := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_disjiUnion,F]
    constructor
    · rintro ⟨⟨hp,hq⟩,he⟩
      exact ⟨f p.1,hf p.1 hp,⟨hp,rfl⟩,hq,he.symm⟩
    · rintro ⟨v,hv,⟨hp,hfp⟩,hq,hgq⟩
      exact ⟨⟨hp,hq⟩,hfp.trans hgq.symm⟩
  rw [he,Finset.card_disjiUnion]
  simp only [F,Finset.card_product]

theorem fiber_square_sum {α κ : Type*} [DecidableEq κ] (S : Finset α) (U : Finset κ) (f : α → κ)
    (hf : ∀ x ∈ S, f x ∈ U) :
    (∑ v ∈ U, (S.filter (fun x => f x=v)).card^2) =
      ((S ×ˢ S).filter (fun p => f p.1=f p.2)).card := by
  classical
  simpa only [pow_two] using (mixed_fiber_collision S S U f f hf).symm

theorem mixed_fiber_cauchy {α β κ : Type*} [DecidableEq κ] (S : Finset α) (T : Finset β)
    (f : α → κ) (g : β → κ) :
    ((S ×ˢ T).filter (fun p => f p.1=g p.2)).card^2 ≤
      ((S ×ˢ S).filter (fun p => f p.1=f p.2)).card *
      ((T ×ˢ T).filter (fun p => g p.1=g p.2)).card := by
  classical
  let U := S.image f ∪ T.image g
  have hf : ∀ x ∈ S, f x ∈ U := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem f hx)
  have hg : ∀ y ∈ T, g y ∈ U := fun y hy =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem g hy)
  rw [mixed_fiber_collision S T U f g hf,
    ← fiber_square_sum S U f hf, ← fiber_square_sum T U g hg]
  exact Finset.sum_mul_sq_le_sq_mul_sq U _ _

end Erdos52.RSFresh

-- END RSProof/MixedFiber.lean

-- BEGIN RSProof/MultiplicativeCauchy.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

def ratioReorder : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ ((ℝ × ℝ) × (ℝ × ℝ)) where
  toFun p := ((p.1.1,p.2.1),(p.2.2,p.1.2))
  invFun p := ((p.1.1,p.2.2),(p.1.2,p.2.1))
  left_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl

theorem mulEnergy_eq_ratio_collision (A : Finset ℝ) :
    mulEnergy A = (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
      (fun p => p.1.1/p.1.2=p.2.1/p.2.2)).card := by
  classical
  have hi : (A ×ˢ A).image (fun p : ℝ × ℝ => p.1/p.2) = A/A := by
    ext t
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_div, Prod.exists]
    aesop
  rw [fiber_collision (A ×ˢ A) (fun p : ℝ × ℝ => p.1/p.2),hi]
  rfl

theorem native_mulEnergy_ratio (A B : Finset ℝ)
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) :
    Finset.mulEnergy A B = (((A ×ˢ A) ×ˢ (B ×ˢ B)).filter
      (fun p => p.1.1/p.1.2=p.2.1/p.2.2)).card := by
  classical
  rw [Finset.mulEnergy_eq_card_filter]
  apply Finset.card_equiv ratioReorder
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [Finset.mem_filter,Finset.mem_product]
  change (((a∈A ∧ b∈B) ∧ c∈A ∧ d∈B) ∧ a*b=c*d) ↔
    (((a∈A ∧ c∈A) ∧ d∈B ∧ b∈B) ∧ a/c=d/b)
  constructor
  · rintro ⟨⟨⟨ha,hb⟩,hc,hd⟩,he⟩
    refine ⟨⟨⟨ha,hc⟩,hd,hb⟩,?_⟩
    apply (div_eq_div_iff (hA c hc) (hB b hb)).mpr
    simpa only [mul_comm] using he
  · rintro ⟨⟨⟨ha,hc⟩,hd,hb⟩,he⟩
    refine ⟨⟨⟨ha,hb⟩,hc,hd⟩,?_⟩
    have hh := (div_eq_div_iff (hA c hc) (hB b hb)).mp he
    simpa only [mul_comm] using hh

theorem multiplicative_mixed_cauchy (A B : Finset ℝ)
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) :
    (Finset.mulEnergy A B)^2 ≤ mulEnergy A * mulEnergy B := by
  classical
  rw [native_mulEnergy_ratio A B hA hB, mulEnergy_eq_ratio_collision,
    mulEnergy_eq_ratio_collision]
  exact mixed_fiber_cauchy (A ×ˢ A) (B ×ˢ B)
    (fun p : ℝ × ℝ => p.1/p.2) (fun p : ℝ × ℝ => p.1/p.2)

theorem product_card_energy (A B : Finset ℝ)
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) :
    A.card^4*B.card^4 ≤ (A*B).card^2*mulEnergy A*mulEnergy B := by
  have hlow := Finset.le_card_mul_mul_mulEnergy A B
  have hsq := Nat.pow_le_pow_left hlow 2
  have hcs := multiplicative_mixed_cauchy A B hA hB
  have hm := Nat.mul_le_mul_left ((A*B).card^2) hcs
  nlinarith

end Erdos52.RSFresh

-- END RSProof/MultiplicativeCauchy.lean

-- BEGIN RSProof/EnergySlopeClass.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem positive_mulEnergy_lower (A : Finset ℝ) (hA : Positive A) :
    A.card^4 ≤ (A*A).card*mulEnergy A := by
  have he : Finset.mulEnergy A A = mulEnergy A := by
    rw [native_mulEnergy_ratio A A (fun x hx => ne_of_gt (hA x hx))
      (fun x hx => ne_of_gt (hA x hx)),mulEnergy_eq_ratio_collision]
  have hh := Finset.le_card_mul_mul_mulEnergy A A
  rw [he] at hh
  nlinarith

theorem positive_mulEnergy_pos (A : Finset ℝ) (hA : Positive A) (hn : A.Nonempty) :
    0 < mulEnergy A := by
  have hh := positive_mulEnergy_lower A hA
  have hp := hn.card_pos
  by_contra he
  have hz : mulEnergy A=0 := by omega
  rw [hz,mul_zero] at hh
  exact (Nat.not_le_of_gt (pow_pos hp 4)) hh

theorem exists_energy_slope_class (A : Finset ℝ) (hA : Positive A) (hn : A.Nonempty) :
    ∃ S ⊆ A/A, S.Nonempty ∧ ∃ τ : ℕ, 0 < τ ∧ τ ≤ A.card ∧
      (∀ t ∈ S, τ ≤ (slopeFiber A t).card ∧ (slopeFiber A t).card < 2*τ) ∧
      mulEnergy A ≤ 4*logBudget A.card*S.card*τ^2 := by
  classical
  obtain ⟨j,hj,he⟩ := exists_dyadic_square_class (A/A)
    (fun t => (slopeFiber A t).card) A.card
    (fun t ht => slopeFiber_pos A hA ht) (fun t _ => slopeFiber_card_le A t)
  let S := dyadicClass (A/A) (fun t => (slopeFiber A t).card) j
  have hE : mulEnergy A ≤ 4*logBudget A.card*S.card*(2^j)^2 := by
    rwa [← mulEnergy_slopeFiber A hA] at he
  have hSn : S.Nonempty := by
    by_contra hs
    have hz := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hz,Finset.card_empty,mul_zero,zero_mul] at hE
    exact (Nat.not_le_of_gt (positive_mulEnergy_pos A hA hn)) hE
  have hb : ∀ t ∈ S, 2^j ≤ (slopeFiber A t).card ∧ (slopeFiber A t).card < 2*2^j :=
    fun t ht => dyadicClass_bounds (A/A) (fun t => (slopeFiber A t).card)
      (fun t ht => slopeFiber_pos A hA ht) j ht
  obtain ⟨t,ht⟩ := hSn
  refine ⟨S,Finset.filter_subset _ _,⟨t,ht⟩,2^j,by positivity,
    (hb t ht).1.trans (slopeFiber_card_le A t),hb,hE⟩

end Erdos52.RSFresh

-- END RSProof/EnergySlopeClass.lean

-- BEGIN RSProof/SlopeCollision.lean

namespace Erdos52.RSFresh

noncomputable def collisionCoeff (a b c : ℝ) : ℝ := (a-c)/(b-c)

theorem collisionCoeff_ne_zero (a b c : ℝ) (hac : a ≠ c) (hbc : b ≠ c) :
    collisionCoeff a b c ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr hac) (sub_ne_zero.mpr hbc)

theorem slope_collision_eliminate (a b c d x y z w : ℝ) (hcd : c ≠ d)
    (he : slopeMix a b (x,y) = slopeMix c d (z,w)) :
    z = collisionCoeff a c d*x + collisionCoeff b c d*y := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change x+y=z+w at hx
  change a*x+b*y=c*z+d*w at hy
  unfold collisionCoeff
  have hh : z*(c-d) = (a-d)*x+(b-d)*y := by
    linear_combination -hy + d * hx
  calc
    z = ((a-d)*x+(b-d)*y)/(c-d) := (eq_div_iff (sub_ne_zero.mpr hcd)).mpr hh
    _ = (a-d)/(c-d)*x+(b-d)/(c-d)*y := by ring

end Erdos52.RSFresh

-- END RSProof/SlopeCollision.lean

-- BEGIN RSProof/CollisionCount.lean

namespace Erdos52.RSFresh

noncomputable def linearTripleCount (X Y Z : Finset ℝ) (c d : ℝ) : ℕ := by
  classical
  exact (((X ×ˢ Y) ×ˢ Z).filter (fun p => p.2=c*p.1.1+d*p.1.2)).card

theorem slope_intersection_le_triples (A : Finset ℝ) (a b c d : ℝ) (hcd : c ≠ d) :
    (slopeSums A a b ∩ slopeSums A c d).card ≤
      linearTripleCount (slopeFiber A a) (slopeFiber A b) (slopeFiber A c)
        (collisionCoeff a c d) (collisionCoeff b c d) := by
  classical
  let P := (slopeFiber A a) ×ˢ (slopeFiber A b)
  let Q := (slopeFiber A c) ×ˢ (slopeFiber A d)
  let C := (P ×ˢ Q).filter (fun p => slopeMix a b p.1=slopeMix c d p.2)
  have hfirst : (slopeSums A a b ∩ slopeSums A c d).card ≤ C.card := by
    apply Finset.card_le_card_of_surjOn (fun p => slopeMix a b p.1)
    intro v hv
    obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hv
    obtain ⟨p,hp,hep⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hq
    exact ⟨(p,q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,
      hep.trans heq.symm⟩,hep⟩
  apply hfirst.trans
  apply Finset.card_le_card_of_injOn (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (p.1,p.2.1))
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hP,hQ⟩ := Finset.mem_product.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hP,(Finset.mem_product.mp hQ).1⟩,?_⟩
    exact slope_collision_eliminate a b c d p.1.1 p.1.2 p.2.1 p.2.2 hcd he
  · intro p hp q hq he
    have hp' := congrArg Prod.fst (Finset.mem_filter.mp hp).2
    have hq' := congrArg Prod.fst (Finset.mem_filter.mp hq).2
    have h1 : p.1=q.1 := congrArg (fun v : (ℝ × ℝ) × ℝ => v.1) he
    have h2 : p.2.1=q.2.1 := congrArg (fun v : (ℝ × ℝ) × ℝ => v.2) he
    apply Prod.ext h1
    apply Prod.ext h2
    change p.1.1+p.1.2=p.2.1+p.2.2 at hp'
    change q.1.1+q.1.2=q.2.1+q.2.2 at hq'
    rw [h1] at hp'
    linarith

end Erdos52.RSFresh

-- END RSProof/CollisionCount.lean

-- BEGIN RSProof/UnionOverlap.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem union_overlap_bound {ι α : Type*} [DecidableEq α]
    (S : Finset ι) (F : ι → Finset α) (T : ℝ) (hT : 0 ≤ T)
    (hp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((F i ∩ F j).card : ℝ) ≤ T) :
    (∑ i ∈ S, ((F i).card : ℝ)) ≤ ((S.biUnion F).card : ℝ) + (S.card : ℝ)^2*T := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hold : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((F i ∩ F j).card : ℝ) ≤ T := by
      intro i hi j hj hij
      exact hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hi := ih hold
    have hinter : ((F a ∩ S.biUnion F).card : ℝ) ≤ (S.card : ℝ)*T := by
      rw [Finset.inter_biUnion]
      calc
        (((S.biUnion (fun i => F a ∩ F i)).card : ℝ)) ≤
            ∑ i ∈ S, ((F a ∩ F i).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le (s := S) (t := fun i => F a ∩ F i))
        _ ≤ ∑ _i ∈ S, T := by
          apply Finset.sum_le_sum
          intro i hi
          exact hp a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
            (by intro he; subst i; exact ha hi)
        _ = (S.card : ℝ)*T := by simp
    have hu : ((F a ∪ S.biUnion F).card : ℝ) + ((F a ∩ S.biUnion F).card : ℝ) =
        (F a).card + ((S.biUnion F).card : ℝ) := by
      exact_mod_cast Finset.card_union_add_card_inter (F a) (S.biUnion F)
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
    push_cast
    have hn : 0 ≤ (S.card : ℝ) := by positivity
    nlinarith

end Erdos52.RSFresh

-- END RSProof/UnionOverlap.lean

-- BEGIN RSProof/BadSlopePairs.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem slopeSums_comm (A : Finset ℝ) (a b : ℝ) : slopeSums A a b = slopeSums A b a := by
  classical
  ext v
  constructor <;> intro hv
  · obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨(y,x),Finset.mem_product.mpr (Finset.mem_product.mp hxy).symm,?_⟩
    apply Prod.ext <;> dsimp [slopeMix] <;> ring
  · obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨(y,x),Finset.mem_product.mpr (Finset.mem_product.mp hxy).symm,?_⟩
    apply Prod.ext <;> dsimp [slopeMix] <;> ring

theorem bad_cross_pair_intersection (A L R : Finset ℝ) (T : ℝ)
    (hsep : ∀ a ∈ L, ∀ b ∈ R, a < b)
    (hbad : ∀ a ∈ L ∪ R, ∀ b ∈ L ∪ R, ∀ c ∈ L ∪ R, ∀ d ∈ L ∪ R,
      a ≠ b → a ≠ d → b ≠ d → c ≠ d →
      (linearTripleCount (slopeFiber A a) (slopeFiber A b) (slopeFiber A c)
        (collisionCoeff a c d) (collisionCoeff b c d) : ℝ) ≤ T)
    {p q : ℝ × ℝ} (hp : p ∈ L ×ˢ R) (hq : q ∈ L ×ˢ R) (hne : p ≠ q) :
    ((slopeSums A p.1 p.2 ∩ slopeSums A q.1 q.2).card : ℝ) ≤ T := by
  classical
  obtain ⟨hpL,hpR⟩ := Finset.mem_product.mp hp
  obtain ⟨hqL,hqR⟩ := Finset.mem_product.mp hq
  have hp12 := ne_of_lt (hsep _ hpL _ hpR)
  have hq12 := ne_of_lt (hsep _ hqL _ hqR)
  by_cases h2 : p.2=q.2
  · have h1 : p.1 ≠ q.1 := by
      intro h
      exact hne (Prod.ext h h2)
    rw [slopeSums_comm A p.1 p.2, slopeSums_comm A q.1 q.2]
    have hc := slope_intersection_le_triples A p.2 p.1 q.2 q.1 hq12.symm
    have hh := hbad p.2 (Finset.mem_union_right _ hpR)
      p.1 (Finset.mem_union_left _ hpL) q.2 (Finset.mem_union_right _ hqR)
      q.1 (Finset.mem_union_left _ hqL) hp12.symm
      (by rw [h2]; exact hq12.symm) h1 hq12.symm
    exact le_trans (by exact_mod_cast hc) hh
  · have hc := slope_intersection_le_triples A p.1 p.2 q.1 q.2 hq12
    have hh := hbad p.1 (Finset.mem_union_left _ hpL)
      p.2 (Finset.mem_union_right _ hpR) q.1 (Finset.mem_union_left _ hqL)
      q.2 (Finset.mem_union_right _ hqR) hp12
      (ne_of_lt (hsep _ hpL _ hqR)) h2 hq12
    exact le_trans (by exact_mod_cast hc) hh

end Erdos52.RSFresh

-- END RSProof/BadSlopePairs.lean

-- BEGIN RSProof/SlopeBlocks.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def slopeBlockSums (A L R : Finset ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (L ×ˢ R).biUnion (fun p => slopeSums A p.1 p.2)

theorem slopeBlockSums_subset (A L R : Finset ℝ) :
    slopeBlockSums A L R ⊆ (A+A) ×ˢ (A+A) := by
  classical
  intro v hv
  obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
  exact slopeSums_subset A p.1 p.2 hv

theorem slopeBlockSums_mass (A L R : Finset ℝ) (τ : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hsep : ∀ a ∈ L, ∀ b ∈ R, a < b)
    (hτL : ∀ a ∈ L, τ ≤ (slopeFiber A a).card)
    (hτR : ∀ a ∈ R, τ ≤ (slopeFiber A a).card)
    (hpair : ∀ p ∈ L ×ˢ R, ∀ q ∈ L ×ˢ R, p ≠ q →
      ((slopeSums A p.1 p.2 ∩ slopeSums A q.1 q.2).card : ℝ) ≤ T) :
    (L.card : ℝ)*R.card*(τ : ℝ)^2 ≤ (slopeBlockSums A L R).card +
      ((L.card : ℝ)*R.card)^2*T := by
  classical
  have hu := union_overlap_bound (L ×ˢ R) (fun p => slopeSums A p.1 p.2) T hT hpair
  have hlo : (L.card : ℝ)*R.card*(τ : ℝ)^2 ≤
      ∑ p ∈ L ×ˢ R, ((slopeSums A p.1 p.2).card : ℝ) := by
    calc
      (L.card : ℝ)*R.card*(τ : ℝ)^2 = ∑ _p ∈ L ×ˢ R, (τ : ℝ)^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpL,hpR⟩ := Finset.mem_product.mp hp
        rw [slopeSums_card A p.1 p.2 (ne_of_lt (hsep _ hpL _ hpR))]
        exact_mod_cast (show τ^2 ≤ (slopeFiber A p.1).card*(slopeFiber A p.2).card from
          by simpa only [pow_two] using Nat.mul_le_mul (hτL _ hpL) (hτR _ hpR))
  have he : ((L ×ˢ R).card : ℝ) = (L.card : ℝ)*R.card := by simp
  rw [he] at hu
  exact hlo.trans hu

theorem slopeBlockSums_disjoint (A : Finset ℝ) (hA : Positive A)
    (L R U V : Finset ℝ)
    (hLR : ∀ a ∈ L, ∀ b ∈ R, a < b)
    (hUV : ∀ a ∈ U, ∀ b ∈ V, a < b)
    (hRU : ∀ b ∈ R, ∀ c ∈ U, b ≤ c) :
    Disjoint (slopeBlockSums A L R) (slopeBlockSums A U V) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p,hp,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨q,hq,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨hpL,hpR⟩ := Finset.mem_product.mp hp
  obtain ⟨hqL,hqR⟩ := Finset.mem_product.mp hq
  exact Finset.disjoint_left.mp
    (slopeSums_disjoint A hA _ _ _ _ (hLR _ hpL _ hpR) (hRU _ hpR _ hqL)
      (hUV _ hqL _ hqR)) hx hy

end Erdos52.RSFresh

-- END RSProof/SlopeBlocks.lean

-- BEGIN RSProof/OrderedGroups.lean

namespace Erdos52.RSFresh

noncomputable def orderedGroup (lam : ℕ → ℝ) (a b : ℕ) : Finset ℝ := by
  classical
  exact (Finset.Ico a b).image lam

theorem orderedGroup_card (lam : ℕ → ℝ) (N a b : ℕ) (hb : b ≤ N)
    (hmono : ∀ i j, i < j → j < N → lam i < lam j) :
    (orderedGroup lam a b).card = b-a := by
  classical
  rw [orderedGroup, Finset.card_image_iff.mpr]
  · exact Nat.card_Ico a b
  · intro i hi j hj he
    have hi' := Finset.mem_Ico.mp hi
    have hj' := Finset.mem_Ico.mp hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (ne_of_lt (hmono i j h (by omega))) he
    · exact (ne_of_lt (hmono j i h (by omega))) he.symm

theorem orderedGroup_separated (lam : ℕ → ℝ) (N a b c d : ℕ)
    (hbc : b ≤ c) (hd : d ≤ N)
    (hmono : ∀ i j, i < j → j < N → lam i < lam j) :
    ∀ x ∈ orderedGroup lam a b, ∀ y ∈ orderedGroup lam c d, x < y := by
  classical
  intro x hx y hy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  have hi' := Finset.mem_Ico.mp hi
  have hj' := Finset.mem_Ico.mp hj
  exact hmono i j (by omega) (by omega)

theorem orderedGroup_mem {lam : ℕ → ℝ} {a b : ℕ} {x : ℝ}
    (hx : x ∈ orderedGroup lam a b) : ∃ i, a ≤ i ∧ i < b ∧ lam i=x := by
  classical
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
  exact ⟨i,(Finset.mem_Ico.mp hi).1,(Finset.mem_Ico.mp hi).2,he⟩

end Erdos52.RSFresh

-- END RSProof/OrderedGroups.lean

-- BEGIN RSProof/BlockMass.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem block_mass_half (A L R : Finset ℝ) (b τ : ℕ) (hb : 0 < b)
    (hL : L.card=b) (hR : R.card=b)
    (hsep : ∀ a ∈ L, ∀ c ∈ R, a < c)
    (hτL : ∀ a ∈ L, τ ≤ (slopeFiber A a).card)
    (hτR : ∀ a ∈ R, τ ≤ (slopeFiber A a).card)
    (hpair : ∀ p ∈ L ×ˢ R, ∀ q ∈ L ×ˢ R, p ≠ q →
      ((slopeSums A p.1 p.2 ∩ slopeSums A q.1 q.2).card : ℝ) ≤
        (τ : ℝ)^2 / (2*(b : ℝ)^2)) :
    (b : ℝ)^2*(τ : ℝ)^2 ≤ 2*((slopeBlockSums A L R).card : ℝ) := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hh := slopeBlockSums_mass A L R τ ((τ : ℝ)^2/(2*(b : ℝ)^2))
    (by positivity) hsep hτL hτR hpair
  rw [hL,hR] at hh
  have he : ((b : ℝ)*b)^2 * ((τ : ℝ)^2/(2*(b : ℝ)^2)) =
      (b : ℝ)^2*(τ : ℝ)^2/2 := by
    field_simp [ne_of_gt hb']
  rw [he] at hh
  nlinarith

theorem disjoint_blocks_mass (A : Finset ℝ) (hA : Positive A) (q b τ : ℕ)
    (L R : ℕ → Finset ℝ)
    (hsep : ∀ i < q, ∀ a ∈ L i, ∀ c ∈ R i, a < c)
    (horder : ∀ i j, i < j → j < q → ∀ a ∈ R i, ∀ c ∈ L j, a ≤ c)
    (hmass : ∀ i < q, (b : ℝ)^2*(τ : ℝ)^2 ≤
      2*((slopeBlockSums A (L i) (R i)).card : ℝ)) :
    (q : ℝ)*(b : ℝ)^2*(τ : ℝ)^2 ≤ 2*((A+A).card : ℝ)^2 := by
  classical
  let F := fun i => slopeBlockSums A (L i) (R i)
  have hd : (Finset.range q : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact slopeBlockSums_disjoint A hA _ _ _ _ (hsep i hi') (hsep j hj')
        (horder i j h hj')
    · exact (slopeBlockSums_disjoint A hA _ _ _ _ (hsep j hj') (hsep i hi')
        (horder j i h hi')).symm
  have hs : (Finset.range q).disjiUnion F hd ⊆ (A+A) ×ˢ (A+A) := by
    intro v hv
    obtain ⟨i,hi,hv⟩ := Finset.mem_disjiUnion.mp hv
    exact slopeBlockSums_subset A (L i) (R i) hv
  have hu : (∑ i ∈ Finset.range q, ((F i).card : ℝ)) ≤ ((A+A).card : ℝ)^2 := by
    have hc := Finset.card_le_card hs
    rw [Finset.card_disjiUnion, Finset.card_product] at hc
    rw [pow_two]
    exact_mod_cast hc
  have hh : (∑ _i ∈ Finset.range q, (b : ℝ)^2*(τ : ℝ)^2) ≤
      2*∑ i ∈ Finset.range q, ((F i).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hmass i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  nlinarith

end Erdos52.RSFresh

-- END RSProof/BlockMass.lean

-- BEGIN RSProof/BadSlopeBlocks.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem bad_slope_array_bound (A S : Finset ℝ) (hA : Positive A)
    (N b τ : ℕ) (hb : 0 < b) (hN : 4*b ≤ N) (lam : ℕ → ℝ)
    (hmem : ∀ i < N, lam i ∈ S)
    (hmono : ∀ i j, i < j → j < N → lam i < lam j)
    (hτ : ∀ t ∈ S, τ ≤ (slopeFiber A t).card)
    (hbad : ∀ a ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S,
      a ≠ c → a ≠ e → c ≠ e → d ≠ e →
      (linearTripleCount (slopeFiber A a) (slopeFiber A c) (slopeFiber A d)
        (collisionCoeff a d e) (collisionCoeff c d e) : ℝ) ≤
          (τ : ℝ)^2/(2*(b : ℝ)^2)) :
    (N : ℝ)*(b : ℝ)*(τ : ℝ)^2 ≤ 8*((A+A).card : ℝ)^2 := by
  classical
  let q := N/(2*b)
  let L := fun i => orderedGroup lam (2*b*i) (2*b*i+b)
  let R := fun i => orderedGroup lam (2*b*i+b) (2*b*(i+1))
  have hqN : 2*b*q ≤ N := by
    have hh := Nat.div_mul_le_self N (2*b)
    dsimp [q]
    nlinarith
  have hend (i : ℕ) (hi : i < q) : 2*b*(i+1) ≤ N := by
    have hm := Nat.mul_le_mul_left (2*b) (show i+1 ≤ q by omega)
    exact hm.trans hqN
  have hLs (i : ℕ) (hi : i < q) : L i ⊆ S := by
    intro x hx
    obtain ⟨j,hj,hj',rfl⟩ := orderedGroup_mem hx
    exact hmem j (by have := hend i hi; nlinarith)
  have hRs (i : ℕ) (hi : i < q) : R i ⊆ S := by
    intro x hx
    obtain ⟨j,hj,hj',rfl⟩ := orderedGroup_mem hx
    exact hmem j (lt_of_lt_of_le hj' (hend i hi))
  have hsep (i : ℕ) (hi : i < q) : ∀ a ∈ L i, ∀ c ∈ R i, a < c :=
    orderedGroup_separated lam N _ _ _ _ le_rfl (hend i hi) hmono
  have horder (i j : ℕ) (hij : i < j) (hj : j < q) :
      ∀ a ∈ R i, ∀ c ∈ L j, a ≤ c := by
    have hbd : 2*b*(i+1) ≤ 2*b*j := Nat.mul_le_mul_left _ (by omega)
    have hh := orderedGroup_separated lam N (2*b*i+b) (2*b*(i+1))
      (2*b*j) (2*b*j+b) hbd (by have := hend j hj; nlinarith) hmono
    intro a ha c hc
    exact (hh a ha c hc).le
  have hmass (i : ℕ) (hi : i < q) :
      (b : ℝ)^2*(τ : ℝ)^2 ≤ 2*((slopeBlockSums A (L i) (R i)).card : ℝ) := by
    apply block_mass_half A (L i) (R i) b τ hb
    · rw [orderedGroup_card lam N _ _ (by have := hend i hi; nlinarith) hmono]
      omega
    · rw [orderedGroup_card lam N _ _ (hend i hi) hmono]
      have he : 2*b*(i+1) = 2*b*i+2*b := by ring
      rw [he]
      omega
    · exact hsep i hi
    · exact fun a ha => hτ a (hLs i hi ha)
    · exact fun a ha => hτ a (hRs i hi ha)
    · intro p hp r hr hpr
      apply bad_cross_pair_intersection A (L i) (R i) _ (hsep i hi) _ hp hr hpr
      intro a ha c hc d hd e he hac hae hce hde
      have hu : L i ∪ R i ⊆ S := Finset.union_subset (hLs i hi) (hRs i hi)
      exact hbad a (hu ha) c (hu hc) d (hu hd) e (hu he) hac hae hce hde
  have hm := disjoint_blocks_mass A hA q b τ L R hsep horder hmass
  have hmod := Nat.mod_lt N (by omega : 0 < 2*b)
  have hdiv := Nat.mod_add_div N (2*b)
  have hqn : N ≤ 4*b*q := by
    change N % (2*b) + 2*b*q = N at hdiv
    nlinarith
  have hqn' : (N : ℝ) ≤ 4*(b : ℝ)*(q : ℝ) := by exact_mod_cast hqn
  have hs := mul_le_mul_of_nonneg_right hqn' (by positivity : 0 ≤ (b : ℝ)*(τ : ℝ)^2)
  nlinarith

end Erdos52.RSFresh

-- END RSProof/BadSlopeBlocks.lean

-- BEGIN RSProof/GoodSlopes.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem bad_slope_set_bound (A S : Finset ℝ) (hA : Positive A) (b τ : ℕ)
    (hb : 0 < b) (hS : 4*b ≤ S.card)
    (hτ : ∀ t ∈ S, τ ≤ (slopeFiber A t).card)
    (hbad : ∀ a ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S,
      a ≠ c → a ≠ e → c ≠ e → d ≠ e →
      (linearTripleCount (slopeFiber A a) (slopeFiber A c) (slopeFiber A d)
        (collisionCoeff a d e) (collisionCoeff c d e) : ℝ) ≤
          (τ : ℝ)^2/(2*(b : ℝ)^2)) :
    (S.card : ℝ)*(b : ℝ)*(τ : ℝ)^2 ≤ 8*((A+A).card : ℝ)^2 := by
  classical
  let e := S.orderEmbOfFin rfl
  let lam : ℕ → ℝ := fun i => if hi : i < S.card then e ⟨i,hi⟩ else 0
  have he (i : ℕ) (hi : i < S.card) : lam i=e ⟨i,hi⟩ := by
    simp only [lam,dif_pos hi]
  apply bad_slope_array_bound A S hA S.card b τ hb hS lam _ _ hτ hbad
  · intro i hi
    rw [he i hi]
    exact S.orderEmbOfFin_mem rfl _
  · intro i j hij hj
    have hi : i < S.card := lt_trans hij hj
    rw [he i hi,he j hj]
    exact e.strictMono (show (⟨i,hi⟩ : Fin S.card) < ⟨j,hj⟩ from hij)

noncomputable def goodSlopes (A S : Finset ℝ) (T : ℝ) : Finset ℝ := by
  classical
  exact S.filter (fun c => ∃ a ∈ S, ∃ b ∈ S, ∃ d ∈ S,
    a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      T < (linearTripleCount (slopeFiber A a) (slopeFiber A b) (slopeFiber A c)
        (collisionCoeff a c d) (collisionCoeff b c d) : ℝ))

theorem many_good_slopes (A S : Finset ℝ) (hA : Positive A) (b τ : ℕ)
    (hb : 0 < b) (hS : 8*b ≤ S.card)
    (hτ : ∀ t ∈ S, τ ≤ (slopeFiber A t).card)
    (hlarge : 16*((A+A).card : ℝ)^2 < (S.card : ℝ)*(b : ℝ)*(τ : ℝ)^2) :
    S.card < 2*(goodSlopes A S ((τ : ℝ)^2/(2*(b : ℝ)^2))).card := by
  classical
  let T := (τ : ℝ)^2/(2*(b : ℝ)^2)
  let G := goodSlopes A S T
  let B := S \ G
  have hG : G ⊆ S := Finset.filter_subset _ _
  have hc : B.card+G.card=S.card := Finset.card_sdiff_add_card_eq_card hG
  by_contra hnot
  change ¬ S.card < 2*G.card at hnot
  have hhalf : S.card ≤ 2*B.card := by omega
  have hB : 4*b ≤ B.card := by omega
  have hbsub : B ⊆ S := Finset.sdiff_subset
  have hbad : ∀ a ∈ B, ∀ c ∈ B, ∀ d ∈ B, ∀ e ∈ B,
      a ≠ c → a ≠ e → c ≠ e → d ≠ e →
      (linearTripleCount (slopeFiber A a) (slopeFiber A c) (slopeFiber A d)
        (collisionCoeff a d e) (collisionCoeff c d e) : ℝ) ≤ T := by
    intro a ha c hc d hd e he hac hae hce hde
    by_contra hn
    have hh : d ∈ G := Finset.mem_filter.mpr ⟨hbsub hd,
      a,hbsub ha,c,hbsub hc,e,hbsub he,hac,hae,hce,hde,lt_of_not_ge hn⟩
    exact (Finset.mem_sdiff.mp hd).2 hh
  have hm := bad_slope_set_bound A B hA b τ hb hB (fun t ht => hτ t (hbsub ht)) hbad
  have hh : (S.card : ℝ) ≤ 2*(B.card : ℝ) := by exact_mod_cast hhalf
  have hh' := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (b : ℝ)*(τ : ℝ)^2)
  nlinarith

end Erdos52.RSFresh

-- END RSProof/GoodSlopes.lean

-- BEGIN RSProof/DyadicMass.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem dyadic_mass_partition {α : Type*} (S : Finset α) (f : α → ℕ) (n : ℕ)
    (hf : ∀ x ∈ S, f x ≤ n) :
    ∑ j ∈ Finset.range (logBudget n), ∑ x ∈ dyadicClass S f j, f x = ∑ x ∈ S, f x := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro x hx
  apply Finset.mem_range.mpr
  have hh := Nat.log_mono_right (b := 2) (hf x hx)
  unfold logBudget
  omega

theorem exists_dyadic_mass {α : Type*} (S : Finset α) (f : α → ℕ) (n : ℕ)
    (hbound : ∀ x ∈ S, f x ≤ n) :
    ∃ C ⊆ S, ∃ t : ℕ, 0 < t ∧
      (∀ x ∈ C, t ≤ f x ∧ f x < 2*t) ∧
      (∑ x ∈ S, f x) ≤ 2*logBudget n*C.card*t := by
  classical
  let P := S.filter (fun x => 0 < f x)
  have hP : P ⊆ S := Finset.filter_subset _ _
  have hpos : ∀ x ∈ P, 0 < f x := fun x hx => (Finset.mem_filter.mp hx).2
  have hsum : (∑ x ∈ P, f x) = ∑ x ∈ S, f x := by
    apply Finset.sum_subset hP
    intro x hx hn
    have hh : ¬ 0 < f x := by
      intro h
      exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
    omega
  let g := fun j => ∑ x ∈ dyadicClass P f j, f x
  obtain ⟨j,hj,hmax⟩ := (Finset.range (logBudget n)).exists_max_image g
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (logBudget_pos n)))
  refine ⟨dyadicClass P f j, (Finset.filter_subset _ _).trans hP, 2^j,
    by positivity, fun x hx => dyadicClass_bounds P f hpos j hx, ?_⟩
  have hp := dyadic_mass_partition P f n (fun x hx => hbound x (hP hx))
  have hb : (∑ x ∈ S, f x) ≤ logBudget n*g j := by
    rw [← hsum, ← hp]
    calc
      (∑ i ∈ Finset.range (logBudget n), g i) ≤
          ∑ _i ∈ Finset.range (logBudget n), g j :=
        Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = logBudget n*g j := by simp
  have hg : g j ≤ 2*(dyadicClass P f j).card*2^j := by
    calc
      g j ≤ ∑ _x ∈ dyadicClass P f j, 2*2^j :=
        Finset.sum_le_sum (fun x hx => (dyadicClass_bounds P f hpos j hx).2.le)
      _ = 2*(dyadicClass P f j).card*2^j := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        ring
  have hh := Nat.mul_le_mul_left (logBudget n) hg
  nlinarith

end Erdos52.RSFresh

-- END RSProof/DyadicMass.lean

-- BEGIN RSProof/LinearRepresentations.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def linearCount (X Y : Finset ℝ) (c d z : ℝ) : ℕ := by
  classical
  exact ((X ×ˢ Y).filter (fun p => c*p.1+d*p.2=z)).card

theorem linearCount_le_left (X Y : Finset ℝ) (c d z : ℝ) (hd : d ≠ 0) :
    linearCount X Y c d z ≤ X.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℝ × ℝ => p.1)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq he
    change p.1=q.1 at he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext he
    have hh : d*p.2=d*q.2 := by
      change c*p.1+d*p.2=z at hp'
      change c*q.1+d*q.2=z at hq'
      rw [he] at hp'
      linarith
    exact mul_left_cancel₀ hd hh

theorem linearTripleCount_sum (X Y Z : Finset ℝ) (c d : ℝ) :
    linearTripleCount X Y Z c d = ∑ z ∈ Z, linearCount X Y c d z := by
  classical
  simp only [linearTripleCount, linearCount, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]
  calc
    (∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, if z=c*x+d*y then 1 else 0) =
        ∑ x ∈ X, ∑ z ∈ Z, ∑ y ∈ Y, if z=c*x+d*y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ z ∈ Z, ∑ x ∈ X, ∑ y ∈ Y, if c*x+d*y=z then 1 else 0 := by
      rw [Finset.sum_comm]
      simp only [eq_comm]

theorem exists_popular_linear_subset (X Y Z : Finset ℝ) (c d : ℝ) (hd : d ≠ 0) :
    ∃ C ⊆ Z, ∃ t : ℕ, 0 < t ∧
      (∀ z ∈ C, t ≤ linearCount X Y c d z ∧ linearCount X Y c d z < 2*t) ∧
      linearTripleCount X Y Z c d ≤ 2*logBudget X.card*C.card*t := by
  rw [linearTripleCount_sum]
  exact exists_dyadic_mass Z (linearCount X Y c d) X.card
    (fun z _ => linearCount_le_left X Y c d z hd)

end Erdos52.RSFresh

-- END RSProof/LinearRepresentations.lean

-- BEGIN RSProof/LinearDifference.lean

namespace Erdos52.RSFresh

noncomputable def scaledSet (c : ℝ) (X : Finset ℝ) : Finset ℝ := by
  classical
  exact X.image (fun x => c*x)

theorem scaledSet_card (c : ℝ) (hc : c ≠ 0) (X : Finset ℝ) :
    (scaledSet c X).card = X.card := by
  classical
  exact Finset.card_image_of_injective X (mul_right_injective₀ hc)

theorem scaledSet_nonzero (c : ℝ) (hc : c ≠ 0) (X : Finset ℝ)
    (hX : ∀ x ∈ X, x ≠ 0) : ∀ y ∈ scaledSet c X, y ≠ 0 := by
  classical
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact mul_ne_zero hc (hX x hx)

theorem linearCount_eq_diffCount (X Y : Finset ℝ) (c d z : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    linearCount X Y c d z = diffCount (scaledSet c X) (scaledSet (-d) Y) z := by
  classical
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (c*p.1,(-d)*p.2)
  have hf : Function.Injective f := by
    intro p q he
    apply Prod.ext
    · exact mul_left_cancel₀ hc (congrArg Prod.fst he)
    · exact mul_left_cancel₀ (neg_ne_zero.mpr hd) (congrArg Prod.snd he)
  have he : (((X ×ˢ Y).filter (fun p => c*p.1+d*p.2=z)).image f) =
      ((scaledSet c X) ×ˢ (scaledSet (-d) Y)).filter (fun p => p.1-p.2=z) := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,
        Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩,?_⟩
      change c*x-(-d)*y=z
      dsimp at he
      linarith
    · intro hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      obtain ⟨x,hx,hcx⟩ := Finset.mem_image.mp hx
      obtain ⟨y,hy,hdy⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,?_⟩,
        Prod.ext hcx hdy⟩
      change c*x+d*y=z
      rw [← hcx, ← hdy] at he
      linarith
  unfold linearCount
  rw [← Finset.card_image_of_injective _ hf, he]
  rfl

end Erdos52.RSFresh

-- END RSProof/LinearDifference.lean

-- BEGIN RSProof/GoodRepresentation.lean

namespace Erdos52.RSFresh

theorem logBudget_mono {n m : ℕ} (h : n ≤ m) : logBudget n ≤ logBudget m := by
  unfold logBudget
  exact Nat.add_le_add_right (Nat.log_mono_right h) 4

theorem good_slope_representation (A S : Finset ℝ) (hA : Positive A) (τ : ℕ)
    (hupper : ∀ s ∈ S, (slopeFiber A s).card ≤ 2*τ)
    (T : ℝ) (hT : 0 ≤ T) {s : ℝ} (hs : s ∈ goodSlopes A S T) :
    ∃ X Y C : Finset ℝ, ∃ t : ℕ,
      C ⊆ slopeFiber A s ∧ C.Nonempty ∧ 0 < t ∧
      X.card ≤ 2*τ ∧ Y.card ≤ 2*τ ∧
      (∀ x ∈ X, x ≠ 0) ∧ (∀ y ∈ Y, y ≠ 0) ∧
      (∀ z ∈ C, t ≤ diffCount X Y z) ∧
      T < 2*(logBudget A.card : ℝ)*(C.card : ℝ)*(t : ℝ) := by
  classical
  obtain ⟨hs, a,ha,b,hb,d,hd,hab,had,hbd,hsd,hcount⟩ := Finset.mem_filter.mp hs
  let c := collisionCoeff a s d
  let e := collisionCoeff b s d
  have hc : c ≠ 0 := collisionCoeff_ne_zero a s d had hsd
  have he : e ≠ 0 := collisionCoeff_ne_zero b s d hbd hsd
  obtain ⟨C,hC,t,ht,hrep,hmass⟩ := exists_popular_linear_subset
    (slopeFiber A a) (slopeFiber A b) (slopeFiber A s) c e he
  have hlog : logBudget (slopeFiber A a).card ≤ logBudget A.card :=
    logBudget_mono (slopeFiber_card_le A a)
  have hmass' : linearTripleCount (slopeFiber A a) (slopeFiber A b) (slopeFiber A s) c e ≤
      2*logBudget A.card*C.card*t := by
    exact hmass.trans (by gcongr)
  have hmassr : T < 2*(logBudget A.card : ℝ)*(C.card : ℝ)*(t : ℝ) := by
    have hh : (linearTripleCount (slopeFiber A a) (slopeFiber A b) (slopeFiber A s) c e : ℝ) ≤
        2*(logBudget A.card : ℝ)*(C.card : ℝ)*(t : ℝ) := by exact_mod_cast hmass'
    exact hcount.trans_le hh
  have hne : C.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hz, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul] at hmassr
    linarith
  refine ⟨scaledSet c (slopeFiber A a), scaledSet (-e) (slopeFiber A b), C,t,
    hC,hne,ht,?_,?_,?_,?_,?_,hmassr⟩
  · rw [scaledSet_card c hc]
    exact hupper a ha
  · rw [scaledSet_card (-e) (neg_ne_zero.mpr he)]
    exact hupper b hb
  · apply scaledSet_nonzero c hc
    intro x hx
    exact ne_of_gt (hA x (Finset.mem_filter.mp hx).1)
  · apply scaledSet_nonzero (-e) (neg_ne_zero.mpr he)
    intro x hx
    exact ne_of_gt (hA x (Finset.mem_filter.mp hx).1)
  · intro z hz
    rw [← linearCount_eq_diffCount _ _ c e z hc he]
    exact (hrep z hz).1

end Erdos52.RSFresh

-- END RSProof/GoodRepresentation.lean

-- BEGIN RSProof/LargeProductAlgebra.lean

namespace Erdos52.RSFresh

theorem large_product_algebra (n c t p E F D L b s τ : ℝ)
    (hτ : 0 < τ) (hE : 0 ≤ E) (hD : 0 ≤ D) (hL : 0 ≤ L) (_hs : 0 ≤ s)
    (hcs : n^4*c^4 ≤ p^2*E*F)
    (hF : F*t^4 ≤ D*τ^6*L)
    (hEu : E ≤ 4*L*s*τ^2)
    (hreps : τ^2 ≤ 4*b^2*L*c*t) :
    n^4 ≤ 1024*D*p^2*s*b^8*L^6 := by
  have hp := pow_le_pow_left₀ (sq_nonneg τ) hreps 4
  have hp' : τ^8 ≤ 256*b^8*L^4*c^4*t^4 := by
    calc
      τ^8 = (τ^2)^4 := by ring
      _ ≤ (4*b^2*L*c*t)^4 := hp
      _ = 256*b^8*L^4*c^4*t^4 := by ring
  have hct : n^4*c^4*t^4 ≤ 4*D*p^2*s*τ^8*L^2 := by
    calc
      n^4*c^4*t^4 ≤ (p^2*E*F)*t^4 :=
        mul_le_mul_of_nonneg_right hcs (by positivity)
      _ = p^2*E*(F*t^4) := by ring
      _ ≤ p^2*E*(D*τ^6*L) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
      _ = E*(p^2*D*τ^6*L) := by ring
      _ ≤ (4*L*s*τ^2)*(p^2*D*τ^6*L) :=
        mul_le_mul_of_nonneg_right hEu (by positivity)
      _ = 4*D*p^2*s*τ^8*L^2 := by ring
  have hh : n^4*τ^8 ≤ (1024*D*p^2*s*b^8*L^6)*τ^8 := by
    calc
      n^4*τ^8 ≤ n^4*(256*b^8*L^4*c^4*t^4) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = (256*b^8*L^4)*(n^4*c^4*t^4) := by ring
      _ ≤ (256*b^8*L^4)*(4*D*p^2*s*τ^8*L^2) :=
        mul_le_mul_of_nonneg_left hct (by positivity)
      _ = (1024*D*p^2*s*b^8*L^6)*τ^8 := by ring
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < τ^8)).mp hh

end Erdos52.RSFresh

-- END RSProof/LargeProductAlgebra.lean

-- BEGIN RSProof/GoodProductBound.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem good_slope_product_bound (A S : Finset ℝ) (hA : Positive A) (b τ : ℕ)
    (hb : 0 < b) (hτ : 0 < τ) (D : ℝ) (hD : 0 ≤ D)
    (hupper : ∀ s ∈ S, (slopeFiber A s).card ≤ 2*τ)
    (hE : (mulEnergy A : ℝ) ≤ 4*(logBudget A.card : ℝ)*(S.card : ℝ)*(τ : ℝ)^2)
    (hrep : ∀ X Y C : Finset ℝ, ∀ t : ℕ, C.Nonempty → 0 < t →
      X.card ≤ 2*τ → Y.card ≤ 2*τ →
      (∀ x ∈ X, x ≠ 0) → (∀ y ∈ Y, y ≠ 0) → (∀ z ∈ C, z ≠ 0) →
      (∀ z ∈ C, t ≤ diffCount X Y z) →
      (mulEnergy C : ℝ)*(t : ℝ)^4 ≤ D*(τ : ℝ)^6*(logBudget A.card : ℝ))
    {s : ℝ} (hs : s ∈ goodSlopes A S ((τ : ℝ)^2/(2*(b : ℝ)^2))) :
    (A.card : ℝ)^4 ≤ 1024*D*((A*slopeFiber A s).card : ℝ)^2*
      (S.card : ℝ)*(b : ℝ)^8*(logBudget A.card : ℝ)^6 := by
  classical
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hτ' : 0 < (τ : ℝ) := by exact_mod_cast hτ
  obtain ⟨X,Y,C,t,hC,hne,ht,hX,hY,hX0,hY0,htrep,hmass⟩ :=
    good_slope_representation A S hA τ hupper _ (by positivity) hs
  have hC0 : ∀ z ∈ C, z ≠ 0 := by
    intro z hz
    exact ne_of_gt (hA z (Finset.mem_filter.mp (hC hz)).1)
  have hA0 : ∀ z ∈ A, z ≠ 0 := fun z hz => ne_of_gt (hA z hz)
  have hc := product_card_energy A C hA0 hC0
  have hcr : (A.card : ℝ)^4*(C.card : ℝ)^4 ≤
      ((A*C).card : ℝ)^2*(mulEnergy A : ℝ)*(mulEnergy C : ℝ) := by exact_mod_cast hc
  have hF := hrep X Y C t hne ht hX hY hX0 hY0 hC0 htrep
  have hm : (τ : ℝ)^2 ≤ 4*(b : ℝ)^2*(logBudget A.card : ℝ)*(C.card : ℝ)*(t : ℝ) := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2*(b : ℝ)^2)).mp hmass
    nlinarith
  have hp := large_product_algebra (A.card : ℝ) (C.card : ℝ) (t : ℝ)
    ((A*C).card : ℝ) (mulEnergy A : ℝ) (mulEnergy C : ℝ) D
    (logBudget A.card : ℝ) (b : ℝ) (S.card : ℝ) (τ : ℝ)
    hτ' (by positivity) hD (by positivity) (by positivity) hcr hF hE hm
  have hsub : A*C ⊆ A*slopeFiber A s := Finset.mul_subset_mul (Finset.Subset.refl A) hC
  have hcard : ((A*C).card : ℝ) ≤ (A*slopeFiber A s).card := by
    exact_mod_cast Finset.card_le_card hsub
  apply hp.trans
  gcongr

end Erdos52.RSFresh

-- END RSProof/GoodProductBound.lean

-- BEGIN RSProof/PairFiberLift.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem pair_fiber_count {α β κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (S : Finset α) (T : Finset β) (Q : Finset (κ × ι)) (f : α → κ) (g : β → ι) :
    ((S ×ˢ T).filter (fun p => (f p.1,g p.2) ∈ Q)).card =
      ∑ q ∈ Q, (S.filter (fun x => f x=q.1)).card*(T.filter (fun y => g y=q.2)).card := by
  classical
  let F := fun q : κ × ι => (S.filter (fun x => f x=q.1)) ×ˢ
    (T.filter (fun y => g y=q.2))
  have hd : (Q : Set (κ × ι)).PairwiseDisjoint F := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨hpa,hpb⟩ := Finset.mem_product.mp hp
    obtain ⟨hqa,hqb⟩ := Finset.mem_product.mp hq
    apply hab
    exact Prod.ext ((Finset.mem_filter.mp hpa).2.symm.trans (Finset.mem_filter.mp hqa).2)
      ((Finset.mem_filter.mp hpb).2.symm.trans (Finset.mem_filter.mp hqb).2)
  have he : (S ×ˢ T).filter (fun p => (f p.1,g p.2) ∈ Q) = Q.disjiUnion F hd := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_disjiUnion,F]
    constructor
    · rintro ⟨⟨hp,hq⟩,hr⟩
      exact ⟨(f p.1,g p.2),hr,⟨hp,rfl⟩,hq,rfl⟩
    · rintro ⟨q,hq,⟨hp,hfp⟩,hr,hgr⟩
      exact ⟨⟨hp,hr⟩,by simpa only [hfp,hgr] using hq⟩
  rw [he,Finset.card_disjiUnion]
  simp only [F,Finset.card_product]

theorem pair_fiber_lower {α β κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (S : Finset α) (T : Finset β) (Q : Finset (κ × ι)) (f : α → κ) (g : β → ι)
    (u v : ℕ)
    (hf : ∀ q ∈ Q, u ≤ (S.filter (fun x => f x=q.1)).card)
    (hg : ∀ q ∈ Q, v ≤ (T.filter (fun y => g y=q.2)).card) :
    Q.card*u*v ≤ ((S ×ˢ T).filter (fun p => (f p.1,g p.2) ∈ Q)).card := by
  classical
  rw [pair_fiber_count]
  calc
    Q.card*u*v = ∑ _q ∈ Q, u*v := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun q hq => Nat.mul_le_mul (hf q hq) (hg q hq))

end Erdos52.RSFresh

-- END RSProof/PairFiberLift.lean

-- BEGIN RSProof/FiberSubset.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem fiber_square_sum_le {α κ : Type*} [DecidableEq κ]
    (S : Finset α) (U : Finset κ) (f : α → κ) :
    (∑ v ∈ U, (S.filter (fun x => f x=v)).card^2) ≤
      ((S ×ˢ S).filter (fun p => f p.1=f p.2)).card := by
  classical
  let V := U ∪ S.image f
  have hm : ∀ x ∈ S, f x ∈ V := fun x hx =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem f hx)
  rw [← fiber_square_sum S V f hm]
  exact Finset.sum_le_sum_of_subset (Finset.subset_union_left)

end Erdos52.RSFresh

-- END RSProof/FiberSubset.lean

-- BEGIN RSProof/RayRepresentation.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def rayRatio (c p : ℝ × ℝ) : ℝ := (c.2-p.2)/(p.1-c.1)

noncomputable def rayPoints (X Y : Finset ℝ) (c : ℝ × ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (X ×ˢ Y).filter (fun p => p.1 ≠ c.1 ∧ c.2 ≠ p.2)

noncomputable def rayCount (X Y : Finset ℝ) (c : ℝ × ℝ) (t : ℝ) : ℕ := by
  classical
  exact ((rayPoints X Y c).filter (fun p => rayRatio c p=t)).card

noncomputable def rayCollision (X Y : Finset ℝ) (c : ℝ × ℝ) : ℕ := by
  classical
  exact (((rayPoints X Y c) ×ˢ (rayPoints X Y c)).filter
    (fun p => rayRatio c p.1=rayRatio c p.2)).card

theorem ray_ratio_lift (A X Y : Finset ℝ) (T : ℕ)
    (hA : ∀ a ∈ A, a ≠ 0) (hrep : ∀ a ∈ A, T ≤ diffCount X Y a) (t : ℝ) :
    ratioCount A A t*T^2 ≤ ∑ c ∈ Y ×ˢ X, rayCount X Y c t := by
  classical
  let Q := (A ×ˢ A).filter (fun p => p.1/p.2=t)
  let R := ((X ×ˢ Y) ×ˢ (X ×ˢ Y)).filter
    (fun p => (p.1.1-p.1.2,p.2.1-p.2.2) ∈ Q)
  have hl : ratioCount A A t*T^2 ≤ R.card := by
    have hh := pair_fiber_lower (X ×ˢ Y) (X ×ˢ Y) Q
      (fun p : ℝ × ℝ => p.1-p.2) (fun p : ℝ × ℝ => p.1-p.2) T T
      (fun q hq => hrep q.1 (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hrep q.2 (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)
    simpa only [pow_two, Nat.mul_assoc, Q, R, ratioCount] using hh
  let U := ((Y ×ˢ X) ×ˢ (X ×ˢ Y)).filter
    (fun p => p.2 ∈ rayPoints X Y p.1 ∧ rayRatio p.1 p.2=t)
  have hu : R.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((p.2.2,p.1.1),(p.2.1,p.1.2)))
    · intro p hp
      obtain ⟨hp,hQ⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp hp
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hq
      obtain ⟨hAq,ht⟩ := Finset.mem_filter.mp hQ
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp hAq
      have hn1 := hA _ h1
      have hn2 := hA _ h2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hv,hx⟩,
        Finset.mem_product.mpr ⟨hu,hy⟩⟩,?_,ht⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hy⟩,
        sub_ne_zero.mp hn2,sub_ne_zero.mp hn1⟩
    · intro p hp q hq he
      have h1 := congrArg (fun v : (ℝ × ℝ) × (ℝ × ℝ) => v.1.1) he
      have h2 := congrArg (fun v : (ℝ × ℝ) × (ℝ × ℝ) => v.1.2) he
      have h3 := congrArg (fun v : (ℝ × ℝ) × (ℝ × ℝ) => v.2.1) he
      have h4 := congrArg (fun v : (ℝ × ℝ) × (ℝ × ℝ) => v.2.2) he
      exact Prod.ext (Prod.ext h2 h4) (Prod.ext h3 h1)
  have he : U.card = ∑ c ∈ Y ×ˢ X, rayCount X Y c t := by
    simp only [U,rayCount,rayPoints,Finset.card_eq_sum_ones,Finset.sum_filter,
      Finset.sum_product,Finset.mem_filter,Finset.mem_product]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    simp only [hu,hv,true_and,ite_and]
  exact hl.trans (hu.trans_eq he)

end Erdos52.RSFresh

-- END RSProof/RayRepresentation.lean

-- BEGIN RSProof/RayEnergyLift.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem representation_energy_lift (A X Y : Finset ℝ) (T : ℕ)
    (hA : ∀ a ∈ A, a ≠ 0) (hrep : ∀ a ∈ A, T ≤ diffCount X Y a) :
    mulEnergy A*T^4 ≤ X.card*Y.card * ∑ c ∈ Y ×ˢ X, rayCollision X Y c := by
  classical
  have hfirst : mulEnergy A*T^4 ≤
      ∑ t ∈ A/A, (∑ c ∈ Y ×ˢ X, rayCount X Y c t)^2 := by
    calc
      mulEnergy A*T^4 = ∑ t ∈ A/A, (ratioCount A A t*T^2)^2 := by
        unfold mulEnergy
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ ≤ _ := Finset.sum_le_sum (fun t ht =>
        Nat.pow_le_pow_left (ray_ratio_lift A X Y T hA hrep t) 2)
  have hcs (t : ℝ) : (∑ c ∈ Y ×ˢ X, rayCount X Y c t)^2 ≤
      X.card*Y.card * ∑ c ∈ Y ×ˢ X, (rayCount X Y c t)^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Y ×ˢ X)
      (fun _ => (1 : ℕ)) (fun c => rayCount X Y c t)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_product,
      nsmul_eq_mul,Nat.cast_id,mul_one,Nat.mul_comm Y.card X.card] using hh
  have hsum : (∑ t ∈ A/A, ∑ c ∈ Y ×ˢ X, (rayCount X Y c t)^2) ≤
      ∑ c ∈ Y ×ˢ X, rayCollision X Y c := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro c hc
    exact fiber_square_sum_le (rayPoints X Y c) (A/A) (rayRatio c)
  calc
    mulEnergy A*T^4 ≤ ∑ t ∈ A/A, (∑ c ∈ Y ×ˢ X, rayCount X Y c t)^2 := hfirst
    _ ≤ ∑ t ∈ A/A, X.card*Y.card * ∑ c ∈ Y ×ˢ X, (rayCount X Y c t)^2 :=
      Finset.sum_le_sum (fun t ht => hcs t)
    _ = X.card*Y.card * ∑ t ∈ A/A, ∑ c ∈ Y ×ˢ X, (rayCount X Y c t)^2 := by
      rw [Finset.mul_sum]
    _ ≤ X.card*Y.card * ∑ c ∈ Y ×ˢ X, rayCollision X Y c :=
      Nat.mul_le_mul_left _ hsum

end Erdos52.RSFresh

-- END RSProof/RayEnergyLift.lean

-- BEGIN RSProof/GapCounting.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem bad_gap_count {ι : Type*} [Fintype ι] (g : ι → ℕ) (k M : ℕ)
    (hs : ∑ i, g i ≤ M) :
    4 * ((Finset.univ.filter (fun i => 4*M < k*g i)).card) ≤ k := by
  classical
  let B := Finset.univ.filter (fun i => 4*M < k*g i)
  have hlow : B.card*(4*M+1) ≤ ∑ i ∈ B, k*g i := by
    calc
      _ = ∑ _i ∈ B, (4*M+1) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have h := (Finset.mem_filter.mp hi).2
        omega
  have hu : (∑ i ∈ B, k*g i) ≤ k*M := by
    calc
      _ ≤ ∑ i, k*g i := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = k * ∑ i, g i := by rw [Finset.mul_sum]
      _ ≤ k*M := Nat.mul_le_mul_left k hs
  change 4*B.card ≤ k
  by_contra h
  have hb : 0 < B.card := by omega
  have hk : k+1 ≤ 4*B.card := by omega
  nlinarith

 theorem two_good_gap_count {ι : Type*} [Fintype ι] (g h : ι → ℕ) (k M N : ℕ)
    (hk : 4 ≤ k) (hc : Fintype.card ι = k-1)
    (hg : ∑ i, g i ≤ M) (hh : ∑ i, h i ≤ N) :
    k ≤ 4 * ((Finset.univ.filter (fun i => k*g i ≤ 4*M ∧ k*h i ≤ 4*N)).card) := by
  classical
  let B := Finset.univ.filter (fun i => 4*M < k*g i)
  let C := Finset.univ.filter (fun i => 4*N < k*h i)
  let G := Finset.univ.filter (fun i => k*g i ≤ 4*M ∧ k*h i ≤ 4*N)
  have hu : (Finset.univ : Finset ι) ⊆ G ∪ B ∪ C := by
    intro i hi
    simp only [G,B,C,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hcard : Fintype.card ι ≤ G.card+B.card+C.card := by
    calc
      _ ≤ (G ∪ B ∪ C).card := Finset.card_le_card hu
      _ ≤ (G ∪ B).card+C.card := Finset.card_union_le _ _
      _ ≤ G.card+B.card+C.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hb := bad_gap_count g k M hg
  have hd := bad_gap_count h k N hh
  change k ≤ 4*G.card
  change 4*B.card ≤ k at hb
  change 4*C.card ≤ k at hd
  omega

end Erdos52.RSFresh

-- END RSProof/GapCounting.lean

-- BEGIN RSProof/SequenceGaps.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem sum_adjacent_gap (n : ℕ) (f : Fin (n+1) → ℕ) (hf : Monotone f) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n)-f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have ht : Monotone (fun i : Fin (n+1) => f i.succ) := fun _ _ h => hf (Nat.succ_le_succ h)
    have h := ih (fun i => f i.succ) ht
    have h01 : f 0 ≤ f (Fin.succ 0) := hf (Fin.zero_le _)
    have h1n : f (Fin.succ 0) ≤ f (Fin.last (n+1)) := hf (Fin.le_last _)
    simpa only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero] using (show
      (f (Fin.succ 0)-f 0) + ∑ i : Fin n, (f i.succ.succ-f i.castSucc.succ) =
        f (Fin.last (n+1))-f 0 by
        rw [h]
        change (f (Fin.succ 0)-f 0) + (f (Fin.last (n+1))-f (Fin.succ 0)) = _
        omega)

 theorem sum_adjacent_gap_le (n M : ℕ) (f : Fin (n+1) → ℕ)
    (hf : Monotone f) (hM : ∀ i, f i ≤ M) :
    ∑ i : Fin n, (f i.succ-f i.castSucc) ≤ M := by
  rw [sum_adjacent_gap n f hf]
  exact (Nat.sub_le _ _).trans (hM _)

 theorem sum_reverse_gap_le (n M : ℕ) (f : Fin (n+1) → ℕ)
    (hf : Antitone f) (hM : ∀ i, f i ≤ M) :
    ∑ i : Fin n, (f i.castSucc-f i.succ) ≤ M := by
  let g : Fin (n+1) → ℕ := fun i => M-f i
  have hg : Monotone g := fun i j hij => Nat.sub_le_sub_left (hf hij) M
  have hs := sum_adjacent_gap_le n M g hg (fun _ => Nat.sub_le _ _)
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [g]
  have ha := hM i.castSucc
  have hb := hM i.succ
  have hc := hf (Fin.castSucc_le_succ i)
  omega

end Erdos52.RSFresh

-- END RSProof/SequenceGaps.lean

-- BEGIN RSProof/RankBasics.lean

namespace Erdos52.RSFresh

noncomputable def rank (A : Finset ℝ) (x : ℝ) : ℕ := by
  classical
  exact (A.filter (· < x)).card

theorem rank_mono (A : Finset ℝ) : Monotone (rank A) := by
  classical
  intro x y h
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans_le h⟩

theorem rank_strict {A : Finset ℝ} {x y : ℝ} (hx : x ∈ A) (h : x < y) : rank A x < rank A y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans h⟩
  · intro he
    have hm : x ∈ A.filter (· < y) := Finset.mem_filter.mpr ⟨hx,h⟩
    rw [← he] at hm
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

theorem rank_injective (A : Finset ℝ) : Set.InjOn (rank A) A := by
  intro x hx y hy he
  rcases lt_trichotomy x y with h | h | h
  · exact False.elim ((ne_of_lt (rank_strict hx h)) he)
  · exact h
  · exact False.elim ((ne_of_lt (rank_strict hy h)) he.symm)

theorem rank_lt_card {A : Finset ℝ} {x : ℝ} (hx : x ∈ A) : rank A x < A.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have hm : x ∈ A.filter (· < x) := he.symm ▸ hx
  exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

theorem rank_window_card (A : Finset ℝ) (r d : ℕ) :
    (A.filter (fun x => r ≤ rank A x+d ∧ rank A x ≤ r+d)).card ≤ 2*d+1 := by
  classical
  calc
    _ ≤ (Finset.Icc (r-d) (r+d)).card := by
      apply Finset.card_le_card_of_injOn (rank A)
      · intro x hx
        have h := (Finset.mem_filter.mp hx).2
        exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
      · intro x hx y hy he
        exact rank_injective A (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
    _ ≤ 2*d+1 := by rw [Nat.card_Icc]; omega

end Erdos52.RSFresh

-- END RSProof/RankBasics.lean

-- BEGIN RSProof/AffineLines.lean

namespace Erdos52.RSFresh

 def OnLine (l : ℝ × ℝ) (p : ℝ × ℝ) : Prop := p.2 = l.1*p.1+l.2

 theorem line_unique {l r p q : ℝ × ℝ} (hp : OnLine l p) (hq : OnLine l q)
    (hp' : OnLine r p) (hq' : OnLine r q) (hx : p.1 ≠ q.1) : l=r := by
  dsimp [OnLine] at *
  have hs : (l.1-r.1)*(p.1-q.1)=0 := by nlinarith
  have he : l.1=r.1 := by
    rcases mul_eq_zero.mp hs with h | h
    · linarith
    · exact False.elim (hx (by linarith))
  apply Prod.ext he
  rw [he] at hp
  linarith

 theorem line_y_injective {l : ℝ × ℝ} (hl : l.1 ≠ 0) {p q : ℝ × ℝ}
    (hp : OnLine l p) (hq : OnLine l q) (hy : p.2=q.2) : p=q := by
  dsimp [OnLine] at *
  have he : p.1=q.1 := by
    have h : l.1*(p.1-q.1)=0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hl)
  exact Prod.ext he hy

 theorem line_x_injective {l p q : ℝ × ℝ} (hp : OnLine l p) (hq : OnLine l q)
    (hx : p.1=q.1) : p=q := by
  dsimp [OnLine] at *
  exact Prod.ext hx (by rw [hp,hq,hx])

 theorem line_y_mono {l p q : ℝ × ℝ} (hl : 0 ≤ l.1) (hp : OnLine l p)
    (hq : OnLine l q) (hx : p.1 ≤ q.1) : p.2 ≤ q.2 := by
  dsimp [OnLine] at *
  rw [hp,hq]
  exact add_le_add (mul_le_mul_of_nonneg_left hx hl) le_rfl

 theorem line_y_anti {l p q : ℝ × ℝ} (hl : l.1 ≤ 0) (hp : OnLine l p)
    (hq : OnLine l q) (hx : p.1 ≤ q.1) : q.2 ≤ p.2 := by
  dsimp [OnLine] at *
  rw [hp,hq]
  exact add_le_add (mul_le_mul_of_nonpos_left hx hl) le_rfl

end Erdos52.RSFresh

-- END RSProof/AffineLines.lean

-- BEGIN RSProof/ClosePairs.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def closeNeighbors (A B : Finset ℝ) (d e : ℕ) (p : ℝ × ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (A.filter (fun x => rank A p.1 ≤ rank A x+d ∧ rank A x ≤ rank A p.1+d)) ×ˢ
    (B.filter (fun y => rank B p.2 ≤ rank B y+e ∧ rank B y ≤ rank B p.2+e))

noncomputable def closePairs (A B : Finset ℝ) (d e : ℕ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) := by
  classical
  exact (A ×ˢ B).biUnion (fun p => (closeNeighbors A B d e p).image (fun q => (p,q)))

 theorem closeNeighbors_card (A B : Finset ℝ) (d e : ℕ) (p : ℝ × ℝ) :
    (closeNeighbors A B d e p).card ≤ (2*d+1)*(2*e+1) := by
  classical
  rw [closeNeighbors, Finset.card_product]
  exact Nat.mul_le_mul (rank_window_card A _ _) (rank_window_card B _ _)

 theorem closePairs_card (A B : Finset ℝ) (d e : ℕ) :
    (closePairs A B d e).card ≤ A.card*B.card*((2*d+1)*(2*e+1)) := by
  classical
  calc
    _ ≤ ∑ p ∈ A ×ˢ B, ((closeNeighbors A B d e p).image (fun q => (p,q))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ A ×ˢ B, (2*d+1)*(2*e+1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.card_image_le).trans (closeNeighbors_card A B d e p)
    _ = _ := by simp [Finset.card_product, Nat.mul_assoc]

 theorem mem_closePairs {A B : Finset ℝ} {d e : ℕ} {p q : ℝ × ℝ}
    (hp : p ∈ A ×ˢ B) (hq : q ∈ A ×ˢ B)
    (hx : Nat.dist (rank A p.1) (rank A q.1) ≤ d)
    (hy : Nat.dist (rank B p.2) (rank B q.2) ≤ e) :
    (p,q) ∈ closePairs A B d e := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨p,hp,Finset.mem_image.mpr ⟨q,?_,rfl⟩⟩
  have hqx := (Finset.mem_product.mp hq).1
  have hqy := (Finset.mem_product.mp hq).2
  dsimp [closeNeighbors]
  apply Finset.mem_product.mpr
  simp only [Finset.mem_filter]
  unfold Nat.dist at hx hy
  exact ⟨⟨hqx,by omega,by omega⟩,⟨hqy,by omega,by omega⟩⟩

 theorem quotient_window (M k : ℕ) (hk : k ≤ M) :
    k*(2*(4*M/k)+1) ≤ 9*M := by
  have h := Nat.div_mul_le_self (4*M) k
  nlinarith

end Erdos52.RSFresh

-- END RSProof/ClosePairs.lean

-- BEGIN RSProof/OrderedLineGaps.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem ordered_line_good_gaps (A B : Finset ℝ) (n : ℕ) (hn : 4 ≤ n+1)
    (p : Fin (n+1) → ℝ × ℝ) (l : ℝ × ℝ)
    (hp : ∀ i, p i ∈ A ×ˢ B) (hl : ∀ i, OnLine l (p i))
    (hx : Monotone (fun i => (p i).1)) :
    n+1 ≤ 4 * ((Finset.univ.filter (fun i : Fin n =>
      (n+1)*Nat.dist (rank A (p i.castSucc).1) (rank A (p i.succ).1) ≤ 4*A.card ∧
      (n+1)*Nat.dist (rank B (p i.castSucc).2) (rank B (p i.succ).2) ≤ 4*B.card)).card) := by
  classical
  let f := fun i => rank A (p i).1
  let g := fun i => rank B (p i).2
  have hf : Monotone f := (rank_mono A).comp hx
  have hM : ∀ i, f i ≤ A.card := fun i => (rank_lt_card (Finset.mem_product.mp (hp i)).1).le
  have hN : ∀ i, g i ≤ B.card := fun i => (rank_lt_card (Finset.mem_product.mp (hp i)).2).le
  have hs : ∑ i : Fin n, Nat.dist (f i.castSucc) (f i.succ) ≤ A.card := by
    simp_rw [Nat.dist_eq_sub_of_le (hf (Fin.castSucc_le_succ _))]
    exact sum_adjacent_gap_le n A.card f hf hM
  have ht : ∑ i : Fin n, Nat.dist (g i.castSucc) (g i.succ) ≤ B.card := by
    rcases le_total 0 l.1 with h | h
    · have hg : Monotone g := fun i j hij => rank_mono B (line_y_mono h (hl i) (hl j) (hx hij))
      simp_rw [Nat.dist_eq_sub_of_le (hg (Fin.castSucc_le_succ _))]
      exact sum_adjacent_gap_le n B.card g hg hN
    · have hg : Antitone g := fun i j hij => rank_mono B (line_y_anti h (hl i) (hl j) (hx hij))
      simp_rw [Nat.dist_eq_sub_of_le_right (hg (Fin.castSucc_le_succ _))]
      exact sum_reverse_gap_le n B.card g hg hN
  exact two_good_gap_count _ _ (n+1) A.card B.card hn (by simp) hs ht

end Erdos52.RSFresh

-- END RSProof/OrderedLineGaps.lean

-- BEGIN RSProof/OrderedLinePairs.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem ordered_line_pairs (A B : Finset ℝ) (n k : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n+1)
    (p : Fin (n+1) → ℝ × ℝ) (l : ℝ × ℝ)
    (hp : ∀ i, p i ∈ A ×ˢ B) (hl : ∀ i, OnLine l (p i))
    (hx : StrictMono (fun i => (p i).1)) :
    ∃ P : Finset ((ℝ × ℝ) × (ℝ × ℝ)),
      k ≤ 4*P.card ∧ P ⊆ closePairs A B (4*A.card/k) (4*B.card/k) ∧
      ∀ z ∈ P, OnLine l z.1 ∧ OnLine l z.2 ∧ z.1.1 ≠ z.2.1 := by
  classical
  let I := Finset.univ.filter (fun i : Fin n =>
      (n+1)*Nat.dist (rank A (p i.castSucc).1) (rank A (p i.succ).1) ≤ 4*A.card ∧
      (n+1)*Nat.dist (rank B (p i.castSucc).2) (rank B (p i.succ).2) ≤ 4*B.card)
  let F : Fin n → (ℝ × ℝ) × (ℝ × ℝ) := fun i => (p i.castSucc,p i.succ)
  have hi : Function.Injective F := by
    intro i j hij
    have he := hx.injective (congrArg (fun z => z.1.1) hij)
    exact Fin.ext (congrArg (fun z : Fin (n+1) => z.val) he)
  refine ⟨I.image F, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hi]
    exact hkn.trans (ordered_line_good_gaps A B n (hk.trans hkn) p l hp hl hx.monotone)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hb := (Finset.mem_filter.mp hi).2
    apply mem_closePairs (hp _) (hp _)
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr
      have he := Nat.mul_le_mul_right (Nat.dist (rank A (p i.castSucc).1) (rank A (p i.succ).1)) hkn
      nlinarith [hb.1]
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr
      have he := Nat.mul_le_mul_right (Nat.dist (rank B (p i.castSucc).2) (rank B (p i.succ).2)) hkn
      nlinarith [hb.2]
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨hl _,hl _,ne_of_lt (hx (Fin.castSucc_lt_succ))⟩

end Erdos52.RSFresh

-- END RSProof/OrderedLinePairs.lean

-- BEGIN RSProof/LinePoints.lean

namespace Erdos52.RSFresh

noncomputable def linePoints (A B : Finset ℝ) (l : ℝ × ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (A ×ˢ B).filter (OnLine l)

 theorem linePoints_card_left (A B : Finset ℝ) (l : ℝ × ℝ) :
    (linePoints A B l).card ≤ A.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq he
    exact line_x_injective (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he

 theorem linePoints_card_right (A B : Finset ℝ) (l : ℝ × ℝ) (hl : l.1 ≠ 0) :
    (linePoints A B l).card ≤ B.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq he
    exact line_y_injective hl (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he

 theorem line_lucky_pairs (A B : Finset ℝ) (l : ℝ × ℝ) (k : ℕ)
    (hk : 4 ≤ k) (hc : k ≤ (linePoints A B l).card) :
    ∃ P : Finset ((ℝ × ℝ) × (ℝ × ℝ)),
      k ≤ 4*P.card ∧ P ⊆ closePairs A B (4*A.card/k) (4*B.card/k) ∧
      ∀ z ∈ P, OnLine l z.1 ∧ OnLine l z.2 ∧ z.1.1 ≠ z.2.1 := by
  classical
  let X := (linePoints A B l).image Prod.fst
  have hX : X.card = (linePoints A B l).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    exact line_x_injective (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
  obtain ⟨S,hS,hcS⟩ := Finset.exists_subset_card_eq (hc.trans_eq hX.symm)
  have he : S.card = (k-1)+1 := by omega
  let f := S.orderEmbOfFin he
  let p : Fin ((k-1)+1) → ℝ × ℝ := fun i => (f i,l.1*f i+l.2)
  have hp : ∀ i, p i ∈ A ×ˢ B := by
    intro i
    have hmem := hS (S.orderEmbOfFin_mem he i)
    obtain ⟨q,hq,hqe⟩ := Finset.mem_image.mp hmem
    have hline := (Finset.mem_filter.mp hq).2
    have hgrid := (Finset.mem_filter.mp hq).1
    have heq : p i=q := by
      apply Prod.ext
      · exact hqe.symm
      · dsimp [p]
        dsimp [OnLine] at hline
        rw [← hqe]
        exact hline.symm
    exact heq.symm ▸ hgrid
  exact ordered_line_pairs A B (k-1) k hk (by omega) p l hp (fun _ => rfl) f.strictMono

end Erdos52.RSFresh

-- END RSProof/LinePoints.lean

-- BEGIN RSProof/RayLine.lean

namespace Erdos52.RSFresh

noncomputable def rayLine (c p : ℝ × ℝ) : ℝ × ℝ :=
  (-rayRatio c p, c.2+rayRatio c p*c.1)

theorem rayLine_center (c p : ℝ × ℝ) : OnLine (rayLine c p) c := by
  dsimp [OnLine,rayLine]
  ring

theorem rayLine_point (c p : ℝ × ℝ) (hx : p.1 ≠ c.1) : OnLine (rayLine c p) p := by
  have hh : rayRatio c p*(p.1-c.1)=c.2-p.2 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hx)
  dsimp [OnLine,rayLine]
  nlinarith

theorem rayLine_other (c p q : ℝ × ℝ) (hx : q.1 ≠ c.1)
    (he : rayRatio c p=rayRatio c q) : OnLine (rayLine c p) q := by
  have hh := rayLine_point c q hx
  simpa only [rayLine,he] using hh

theorem rayLine_slope_ne_zero (c p : ℝ × ℝ) (hx : p.1 ≠ c.1) (hy : c.2 ≠ p.2) :
    (rayLine c p).1 ≠ 0 := by
  dsimp [rayLine,rayRatio]
  exact neg_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hy) (sub_ne_zero.mpr hx))

theorem rayLine_rich (X Y : Finset ℝ) (c p q : ℝ × ℝ)
    (hp : p ∈ rayPoints X Y c) (hq : q ∈ rayPoints X Y c)
    (he : rayRatio c p=rayRatio c q) (hne : p ≠ q) :
    2 ≤ (linePoints X Y (rayLine c p)).card := by
  classical
  obtain ⟨hp,hpx,hpy⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq,hqx,hqy⟩ := Finset.mem_filter.mp hq
  have hp' : p ∈ linePoints X Y (rayLine c p) :=
    Finset.mem_filter.mpr ⟨hp,rayLine_point c p hpx⟩
  have hq' : q ∈ linePoints X Y (rayLine c p) :=
    Finset.mem_filter.mpr ⟨hq,rayLine_other c p q hqx he⟩
  have hs : ({p,q} : Finset (ℝ × ℝ)) ⊆ linePoints X Y (rayLine c p) := by
    intro r hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp'
    · exact hq'
  have hh := Finset.card_le_card hs
  simpa only [Finset.card_pair hne] using hh

end Erdos52.RSFresh

-- END RSProof/RayLine.lean

-- BEGIN RSProof/TaggedUnion.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def taggedUnion {α β : Type*} (S : Finset α) (F : α → Finset β) : Finset (α × β) := by
  classical
  exact S.biUnion (fun a => (F a).image (fun b => (a,b)))

theorem mem_taggedUnion {α β : Type*} (S : Finset α) (F : α → Finset β) (p : α × β) :
    p ∈ taggedUnion S F ↔ p.1 ∈ S ∧ p.2 ∈ F p.1 := by
  classical
  rcases p with ⟨a,b⟩
  simp [taggedUnion]

theorem taggedUnion_card {α β : Type*} (S : Finset α) (F : α → Finset β) :
    (taggedUnion S F).card = ∑ a ∈ S, (F a).card := by
  classical
  have hd : (S : Set α).PairwiseDisjoint (fun a => (F a).image (fun b => (a,b))) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hq
    exact hab (congrArg Prod.fst (he.trans hf.symm))
  rw [taggedUnion,Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro a ha
  exact Finset.card_image_of_injective _ (fun x y h => congrArg Prod.snd h)

end Erdos52.RSFresh

-- END RSProof/TaggedUnion.lean

-- BEGIN RSProof/RayTriples.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def rayPairSet (X Y : Finset ℝ) (c : ℝ × ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) := by
  classical
  exact ((rayPoints X Y c) ×ˢ (rayPoints X Y c)).filter
    (fun p => rayRatio c p.1=rayRatio c p.2)

noncomputable def rayTriples (X Y : Finset ℝ) : Finset ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
  taggedUnion (Y ×ˢ X) (rayPairSet X Y)

theorem rayTriples_card (X Y : Finset ℝ) :
    (rayTriples X Y).card = ∑ c ∈ Y ×ˢ X, rayCollision X Y c := by
  rw [rayTriples,taggedUnion_card]
  rfl

theorem rayTriples_mem (X Y : Finset ℝ) (v : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :
    v ∈ rayTriples X Y ↔ v.1 ∈ Y ×ˢ X ∧ v.2.1 ∈ rayPoints X Y v.1 ∧
      v.2.2 ∈ rayPoints X Y v.1 ∧ rayRatio v.1 v.2.1=rayRatio v.1 v.2.2 := by
  classical
  rw [rayTriples,mem_taggedUnion]
  simp only [rayPairSet,Finset.mem_filter,Finset.mem_product,and_assoc]

theorem diagonal_rayTriples_bound (X Y : Finset ℝ) :
    ((rayTriples X Y).filter (fun v => v.2.1=v.2.2)).card ≤ X.card^2*Y.card^2 := by
  classical
  have hh : ((rayTriples X Y).filter (fun v => v.2.1=v.2.2)).card ≤
      ((Y ×ˢ X) ×ˢ (X ×ˢ Y)).card := by
    apply Finset.card_le_card_of_injOn (fun v : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) => (v.1,v.2.1))
    · intro v hv
      have hm := (rayTriples_mem X Y v).mp (Finset.mem_filter.mp hv).1
      exact Finset.mem_product.mpr ⟨hm.1,(Finset.mem_filter.mp hm.2.1).1⟩
    · intro v hv w hw he
      have hv' := (Finset.mem_filter.mp hv).2
      have hw' := (Finset.mem_filter.mp hw).2
      have hc : v.1=w.1 := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1) he
      have hp : v.2.1=w.2.1 := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2) he
      exact Prod.ext hc (Prod.ext hp (hv'.symm.trans (hp.trans hw')))
  simp only [Finset.card_product] at hh
  nlinarith

end Erdos52.RSFresh

-- END RSProof/RayTriples.lean

-- BEGIN RSProof/RayTripleLines.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def offRayTriples (X Y : Finset ℝ) := by
  classical
  exact (rayTriples X Y).filter (fun v => v.2.1 ≠ v.2.2)

noncomputable def rayLines (X Y : Finset ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (offRayTriples X Y).image (fun v => rayLine v.1 v.2.1)

theorem rayLines_slope (X Y : Finset ℝ) {l : ℝ × ℝ} (hl : l ∈ rayLines X Y) : l.1 ≠ 0 := by
  classical
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
  have hm := (rayTriples_mem X Y v).mp (Finset.mem_filter.mp hv).1
  have hp := (Finset.mem_filter.mp hm.2.1).2
  exact rayLine_slope_ne_zero v.1 v.2.1 hp.1 hp.2

theorem rayLines_rich (X Y : Finset ℝ) {l : ℝ × ℝ} (hl : l ∈ rayLines X Y) :
    2 ≤ (linePoints X Y l).card := by
  classical
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨hv,hne⟩ := Finset.mem_filter.mp hv
  have hm := (rayTriples_mem X Y v).mp hv
  exact rayLine_rich X Y v.1 v.2.1 v.2.2 hm.2.1 hm.2.2.1 hm.2.2.2 hne

theorem offRayTriples_bound (X Y : Finset ℝ) :
    (offRayTriples X Y).card ≤ ∑ l ∈ rayLines X Y,
      (linePoints X Y l).card^2*(linePoints Y X l).card := by
  classical
  let F := fun l => (linePoints Y X l) ×ˢ ((linePoints X Y l) ×ˢ (linePoints X Y l))
  have hh : (offRayTriples X Y).card ≤ (taggedUnion (rayLines X Y) F).card := by
    apply Finset.card_le_card_of_injOn
      (fun v : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) => (rayLine v.1 v.2.1,v))
    · intro v hv
      have hm := (rayTriples_mem X Y v).mp (Finset.mem_filter.mp hv).1
      have hp := Finset.mem_filter.mp hm.2.1
      have hq := Finset.mem_filter.mp hm.2.2.1
      apply (mem_taggedUnion _ _ _).mpr
      refine ⟨Finset.mem_image_of_mem _ hv,Finset.mem_product.mpr ⟨?_,Finset.mem_product.mpr ⟨?_,?_⟩⟩⟩
      · exact Finset.mem_filter.mpr ⟨hm.1,rayLine_center v.1 v.2.1⟩
      · exact Finset.mem_filter.mpr ⟨hp.1,rayLine_point v.1 v.2.1 hp.2.1⟩
      · exact Finset.mem_filter.mpr ⟨hq.1,rayLine_other v.1 v.2.1 v.2.2 hq.2.1 hm.2.2.2⟩
    · intro v hv w hw he
      exact congrArg Prod.snd he
  rw [taggedUnion_card] at hh
  have he : (∑ l ∈ rayLines X Y, (F l).card) =
      ∑ l ∈ rayLines X Y, (linePoints X Y l).card^2*(linePoints Y X l).card := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [F,Finset.card_product,pow_two]
    ac_rfl
  exact hh.trans_eq he

theorem rayCollision_sum_bound (X Y : Finset ℝ) :
    (∑ c ∈ Y ×ˢ X, rayCollision X Y c) ≤ X.card^2*Y.card^2 +
      ∑ l ∈ rayLines X Y, (linePoints X Y l).card^2*(linePoints Y X l).card := by
  classical
  rw [← rayTriples_card]
  have hp := Finset.card_filter_add_card_filter_not (s := rayTriples X Y)
    (fun v => v.2.1=v.2.2)
  have hd := diagonal_rayTriples_bound X Y
  have ho := offRayTriples_bound X Y
  change _ + (offRayTriples X Y).card = _ at hp
  omega

end Erdos52.RSFresh

-- END RSProof/RayTripleLines.lean

-- BEGIN RSProof/RichLines.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem rich_lines_bound (A B : Finset ℝ) (L : Finset (ℝ × ℝ)) (k : ℕ)
    (hk : 4 ≤ k) (hs : ∀ l ∈ L, l.1 ≠ 0)
    (hr : ∀ l ∈ L, k ≤ (linePoints A B l).card) :
    k^3*L.card ≤ 324*A.card^2*B.card^2 := by
  classical
  by_cases he : L.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]
  obtain ⟨l0,hl0⟩ := he
  have hkA := (hr l0 hl0).trans (linePoints_card_left A B l0)
  have hkB := (hr l0 hl0).trans (linePoints_card_right A B l0 (hs l0 hl0))
  choose P hP using (fun l : L => line_lucky_pairs A B l k hk (hr l l.2))
  have hd : (↑(Finset.univ : Finset L) : Set L).PairwiseDisjoint P := by
    intro l hl r hrr hne
    apply Finset.disjoint_left.mpr
    intro z hzl hzr
    have h1 := (hP l).2.2 z hzl
    have h2 := (hP r).2.2 z hzr
    exact hne (Subtype.ext (line_unique h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2))
  have hsum : ∑ l : L, (P l).card ≤ (closePairs A B (4*A.card/k) (4*B.card/k)).card := by
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨l,hl,hz⟩ := Finset.mem_biUnion.mp hz
    exact (hP l).2.1 hz
  have hlower : k*L.card ≤ 4*∑ l : L, (P l).card := by
    calc
      _ = ∑ _l : L, k := by simp [Nat.mul_comm]
      _ ≤ ∑ l : L, 4*(P l).card := Finset.sum_le_sum (fun l _ => (hP l).1)
      _ = _ := by rw [Finset.mul_sum]
  have hbound := hlower.trans (Nat.mul_le_mul_left 4 (hsum.trans (closePairs_card A B _ _)))
  have hqa := quotient_window A.card k hkA
  have hqb := quotient_window B.card k hkB
  have hp := Nat.mul_le_mul hqa hqb
  have ht := Nat.mul_le_mul_left (k*k) hbound
  have hu := Nat.mul_le_mul_left (4*A.card*B.card) hp
  nlinarith

end Erdos52.RSFresh

-- END RSProof/RichLines.lean

-- BEGIN RSProof/TwoRichLines.lean

namespace Erdos52.RSFresh

 theorem two_rich_lines_card (A B : Finset ℝ) (L : Finset (ℝ × ℝ))
    (hr : ∀ l ∈ L, 2 ≤ (linePoints A B l).card) :
    L.card ≤ (A.card*B.card)^2 := by
  classical
  have hex (l : L) : ∃ p ∈ linePoints A B l, ∃ q ∈ linePoints A B l, p.1≠q.1 := by
    obtain ⟨p,hp,q,hq,hne⟩ := (Finset.one_lt_card (s := linePoints A B l)).mp (by have := hr l l.2; omega)
    refine ⟨p,hp,q,hq,?_⟩
    intro he
    exact hne (line_x_injective (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he)
  choose p hp q hq hne using hex
  have hc : Fintype.card L ≤ ((A ×ˢ B) ×ˢ (A ×ˢ B)).card := by
    apply Finset.card_le_card_of_injOn (fun l : L => (p l,q l))
    · intro l hl
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp (hp l)).1,(Finset.mem_filter.mp (hq l)).1⟩
    · intro l hl r hrr he
      apply Subtype.ext
      have hp' := congrArg (fun z : (ℝ×ℝ)×(ℝ×ℝ) => z.1) he
      have hq' := congrArg (fun z : (ℝ×ℝ)×(ℝ×ℝ) => z.2) he
      change p l=p r at hp'
      change q l=q r at hq'
      exact line_unique (Finset.mem_filter.mp (hp l)).2 (Finset.mem_filter.mp (hq l)).2
        (hp'.symm ▸ (Finset.mem_filter.mp (hp r)).2)
        (hq'.symm ▸ (Finset.mem_filter.mp (hq r)).2) (hne l)
  simpa [Finset.card_product,pow_two] using hc

 theorem rich_lines_bound_two (A B : Finset ℝ) (L : Finset (ℝ × ℝ)) (k : ℕ)
    (hk : 2 ≤ k) (hs : ∀ l ∈ L, l.1 ≠ 0)
    (hr : ∀ l ∈ L, k ≤ (linePoints A B l).card) :
    k^3*L.card ≤ 324*A.card^2*B.card^2 := by
  by_cases hk4 : 4≤k
  · exact rich_lines_bound A B L k hk4 hs hr
  have hc := two_rich_lines_card A B L (fun l hl => hk.trans (hr l hl))
  have hk3 : k^3 ≤ 27 := by interval_cases k <;> norm_num at *
  have hp := Nat.mul_le_mul hk3 hc
  nlinarith

end Erdos52.RSFresh

-- END RSProof/TwoRichLines.lean

-- BEGIN RSProof/LayerCake.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem truncated_layers (m r M : ℕ) (hm : m ≤ M) :
    m ≤ r + ∑ j ∈ Finset.range M, if r+j < m then 1 else 0 := by
  classical
  have he : (Finset.range M).filter (fun j => r+j < m) = Finset.range (m-r) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, he, Finset.card_range]
  omega

 theorem finite_layer_bound {α : Type*} (S : Finset α) (f : α → ℕ) (r M : ℕ)
    (hM : ∀ x ∈ S, f x ≤ M) :
    (∑ x ∈ S, f x : ℕ) ≤ r*S.card+
      ∑ j ∈ Finset.range M, (S.filter (fun x => r+j < f x)).card := by
  classical
  calc
    _ ≤ ∑ x ∈ S, (r+∑ j ∈ Finset.range M, if r+j < f x then 1 else 0) :=
      Finset.sum_le_sum (fun x hx => truncated_layers (f x) r M (hM x hx))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp [Finset.sum_boole, Nat.mul_comm]

 theorem inverse_cube_step (x : ℝ) (hx : 0 < x) :
    1/(x+1)^3 ≤ 1/x^2-1/(x+1)^2 := by
  have hp : 0 < x+1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hp0 : x+1 ≠ 0 := ne_of_gt hp
  field_simp
  nlinarith [sq_nonneg x]

 theorem inverse_cube_tail (r N : ℕ) (hr : 0 < r) :
    (∑ j ∈ Finset.range N, (1:ℝ)/((r:ℝ)+j+1)^3) ≤ 1/(r:ℝ)^2 := by
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  calc
    _ ≤ ∑ j ∈ Finset.range N, (1/((r:ℝ)+j)^2-1/((r:ℝ)+j+1)^2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact inverse_cube_step _ (by positivity)
    _ = 1/(r:ℝ)^2-1/((r:ℝ)+N)^2 := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero,add_assoc] using
        Finset.sum_range_sub' (fun j : ℕ => (1:ℝ)/((r:ℝ)+j)^2) N
    _ ≤ _ := sub_le_self _ (by positivity)

end Erdos52.RSFresh

-- END RSProof/LayerCake.lean

-- BEGIN RSProof/IncidenceThreshold.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def incidenceCount (A B : Finset ℝ) (L : Finset (ℝ × ℝ)) : ℕ :=
  ∑ l ∈ L, (linePoints A B l).card

 theorem incidence_threshold (A B : Finset ℝ) (L : Finset (ℝ × ℝ))
    (hs : ∀ l ∈ L, l.1 ≠ 0) (r : ℕ) (hr : 3 ≤ r) :
    (incidenceCount A B L : ℝ) ≤ r*(L.card:ℝ)+324*(A.card:ℝ)^2*(B.card:ℝ)^2/(r:ℝ)^2 := by
  classical
  have hbase := finite_layer_bound L (fun l => (linePoints A B l).card) r A.card
    (fun l _ => linePoints_card_left A B l)
  have hr' : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  have htail (j : ℕ) :
      ((L.filter (fun l => r+j < (linePoints A B l).card)).card : ℝ) ≤
        324*(A.card:ℝ)^2*(B.card:ℝ)^2/((r:ℝ)+j+1)^3 := by
    have h := rich_lines_bound A B (L.filter (fun l => r+j < (linePoints A B l).card))
      (r+j+1) (by omega)
      (fun l hl => hs l (Finset.mem_filter.mp hl).1)
      (fun l hl => by have := (Finset.mem_filter.mp hl).2; omega)
    have hp : (0:ℝ)<(r:ℝ)+j+1 := by positivity
    apply (le_div_iff₀ (pow_pos hp 3)).mpr
    exact_mod_cast (by simpa [Nat.mul_comm] using h)
  calc
    _ ≤ (r:ℝ)*L.card+∑ j ∈ Finset.range A.card,
        ((L.filter (fun l => r+j < (linePoints A B l).card)).card : ℝ) := by
      exact_mod_cast hbase
    _ ≤ (r:ℝ)*L.card+∑ j ∈ Finset.range A.card,
        324*(A.card:ℝ)^2*(B.card:ℝ)^2/((r:ℝ)+j+1)^3 := by
      exact add_le_add le_rfl (Finset.sum_le_sum (fun j _ => htail j))
    _ = (r:ℝ)*L.card+(324*(A.card:ℝ)^2*(B.card:ℝ)^2)*
        ∑ j ∈ Finset.range A.card, (1:ℝ)/((r:ℝ)+j+1)^3 := by
      rw [Finset.mul_sum]
      simp only [mul_one_div]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (inverse_cube_tail r A.card (by omega))
        (by positivity : 0 ≤ 324*(A.card:ℝ)^2*(B.card:ℝ)^2)
      simpa only [mul_one_div] using add_le_add le_rfl h

end Erdos52.RSFresh

-- END RSProof/IncidenceThreshold.lean

-- BEGIN RSProof/IncidenceCubic.lean

namespace Erdos52.RSFresh

 theorem threshold_to_cubic (I m : ℕ) (C : ℝ) (hm0 : 0 < m)
    (h : ∀ r : ℕ, 3 ≤ r → (I:ℝ) ≤ r*(m:ℝ)+C/(r:ℝ)^2) :
    I ≤ 8*m ∨ (I:ℝ)^3 ≤ 32*C*(m:ℝ)^2 := by
  by_cases hi : I ≤ 8*m
  · exact Or.inl hi
  right
  let r := I/(2*m)
  have hr : 4 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hrI : 2*m*r ≤ I := by simpa [r,Nat.mul_comm] using Nat.div_mul_le_self I (2*m)
  have hIr : I < 2*m*(r+1) := by
    have hh := Nat.mod_lt I (by omega : 0<2*m)
    have he := Nat.mod_add_div I (2*m)
    dsimp [r]
    nlinarith
  have hIr' : I ≤ 4*m*r := by nlinarith
  have hb := h r (by omega)
  have hr0 : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  have hh : (I:ℝ)*(r:ℝ)^2 ≤ (r:ℝ)*(m:ℝ)*(r:ℝ)^2+C := by
    have := (le_div_iff₀ (pow_pos hr0 2)).mp (show (I:ℝ)-(r:ℝ)*m ≤ C/(r:ℝ)^2 by linarith)
    nlinarith
  have ha : 2*(m:ℝ)*r ≤ I := by exact_mod_cast hrI
  have hc : (I:ℝ) ≤ 4*(m:ℝ)*r := by exact_mod_cast hIr'
  have hd := mul_le_mul_of_nonneg_right ha (sq_nonneg (r:ℝ))
  have he := pow_le_pow_left₀ (by positivity : (0:ℝ)≤I) hc 2
  have hf := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ)≤I)
  have hg := mul_le_mul_of_nonneg_left (show (I:ℝ)*(r:ℝ)^2 ≤ 2*C by nlinarith) (by positivity : 0≤16*(m:ℝ)^2)
  nlinarith

 theorem incidence_cubic (A B : Finset ℝ) (L : Finset (ℝ × ℝ))
    (hs : ∀ l ∈ L, l.1 ≠ 0) :
    incidenceCount A B L ≤ 8*L.card ∨
      (incidenceCount A B L : ℝ)^3 ≤ 10368*(A.card:ℝ)^2*(B.card:ℝ)^2*(L.card:ℝ)^2 := by
  by_cases hm : L.card=0
  · exact Or.inl (by simp [incidenceCount,Finset.card_eq_zero.mp hm])
  have h := threshold_to_cubic (incidenceCount A B L) L.card
    (324*(A.card:ℝ)^2*(B.card:ℝ)^2) (Nat.pos_of_ne_zero hm) (incidence_threshold A B L hs)
  convert h using 1; ring

end Erdos52.RSFresh

-- END RSProof/IncidenceCubic.lean

-- BEGIN RSProof/MixedLineIncidence.lean

namespace Erdos52.RSFresh

 theorem mixed_line_incidence (A B : Finset ℝ) (L : Finset (ℝ × ℝ)) (k : ℕ)
    (hk : 2 ≤ k) (hs : ∀ l ∈ L, l.1 ≠ 0)
    (hr : ∀ l ∈ L, k ≤ (linePoints A B l).card) :
    (k:ℝ)^2*(incidenceCount B A L:ℝ) ≤ 2048*(A.card:ℝ)^2*(B.card:ℝ)^2 := by
  have hc := rich_lines_bound_two A B L k hk hs hr
  have hcr : (k:ℝ)^3*(L.card:ℝ) ≤ 324*(A.card:ℝ)^2*(B.card:ℝ)^2 := by exact_mod_cast hc
  have hk0 : (2:ℝ)≤k := by exact_mod_cast hk
  rcases incidence_cubic B A L hs with hsmall | hbig
  · have hi : (incidenceCount B A L:ℝ) ≤ 8*(L.card:ℝ) := by exact_mod_cast hsmall
    have hh := mul_le_mul_of_nonneg_left hi (sq_nonneg (k:ℝ))
    have hp : 2*(k:ℝ)^2*(L.card:ℝ) ≤ (k:ℝ)^3*(L.card:ℝ) := by
      have := mul_le_mul_of_nonneg_right hk0 (by positivity : 0≤(k:ℝ)^2*(L.card:ℝ))
      nlinarith
    nlinarith
  · apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hbig (by positivity : 0≤(k:ℝ)^6)
    have h2 := pow_le_pow_left₀ (by positivity : 0≤(k:ℝ)^3*(L.card:ℝ)) hcr 2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤10368*(A.card:ℝ)^2*(B.card:ℝ)^2)
    nlinarith [show 0≤(A.card:ℝ)^6*(B.card:ℝ)^6 by positivity]

end Erdos52.RSFresh

-- END RSProof/MixedLineIncidence.lean

-- BEGIN RSProof/MixedCollinear.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem mixed_collinear_bound (A B : Finset ℝ) (L : Finset (ℝ × ℝ))
    (hs : ∀ l ∈ L, l.1 ≠ 0) (hr : ∀ l ∈ L, 2 ≤ (linePoints A B l).card) :
    (∑ l ∈ L, ((linePoints A B l).card:ℝ)^2*(linePoints B A l).card) ≤
      8192*(A.card:ℝ)^2*(B.card:ℝ)^2*logBudget A.card := by
  classical
  let f := fun l => (linePoints A B l).card
  have hp : ∑ j ∈ Finset.range (logBudget A.card),
      ∑ l ∈ dyadicClass L f j, (f l:ℝ)^2*(linePoints B A l).card =
        ∑ l ∈ L, (f l:ℝ)^2*(linePoints B A l).card := by
    apply Finset.sum_fiberwise_of_maps_to
    intro l hl
    apply Finset.mem_range.mpr
    have h := Nat.log_mono_right (b := 2) (linePoints_card_left A B l)
    change Nat.log 2 (f l) ≤ Nat.log 2 A.card at h
    unfold logBudget
    omega
  have hclass (j : ℕ) :
      (∑ l ∈ dyadicClass L f j, (f l:ℝ)^2*(linePoints B A l).card) ≤
        8192*(A.card:ℝ)^2*(B.card:ℝ)^2 := by
    let C := dyadicClass L f j
    change (∑ l ∈ C, (f l:ℝ)^2*(linePoints B A l).card) ≤ _
    by_cases hc : C.Nonempty
    swap
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hc,Finset.sum_empty]
      positivity
    obtain ⟨l,hl⟩ := hc
    have hb := dyadicClass_bounds L f (fun l hl => lt_of_lt_of_le (by decide : 0<2) (hr l hl)) j hl
    have hlL := (Finset.mem_filter.mp hl).1
    have hj : 2 ≤ 2^j := by
      have h := hr l hlL
      change 2 ≤ f l at h
      have hpow : 0 < (2:ℕ)^j := by positivity
      omega
    have hm := mixed_line_incidence A B C (2^j) hj
      (fun l hl => hs l (Finset.mem_filter.mp hl).1)
      (fun l hl => (dyadicClass_bounds L f (fun l hl => lt_of_lt_of_le (by decide : 0<2) (hr l hl)) j hl).1)
    have hsum : (∑ l ∈ C, (f l:ℝ)^2*(linePoints B A l).card) ≤
        4*((2:ℝ)^j)^2*(incidenceCount B A C:ℝ) := by
      calc
        _ ≤ ∑ l ∈ C, 4*((2:ℝ)^j)^2*(linePoints B A l).card := by
          apply Finset.sum_le_sum
          intro l hl
          have hb := (dyadicClass_bounds L f (fun l hl => lt_of_lt_of_le (by decide : 0<2) (hr l hl)) j hl).2
          have hh : (f l:ℝ) ≤ 2*(2:ℝ)^j := by exact_mod_cast hb.le
          have hh2 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤f l) hh 2
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        _ = _ := by rw [← Finset.mul_sum]; simp only [incidenceCount,Nat.cast_sum]
    push_cast at hm
    nlinarith
  change (∑ l ∈ L, (f l:ℝ)^2*(linePoints B A l).card) ≤ _
  rw [← hp]
  calc
    _ ≤ ∑ _j ∈ Finset.range (logBudget A.card), 8192*(A.card:ℝ)^2*(B.card:ℝ)^2 :=
      Finset.sum_le_sum (fun j _ => hclass j)
    _ = _ := by simp; ring

end Erdos52.RSFresh

-- END RSProof/MixedCollinear.lean

-- BEGIN RSProof/DifferenceRepresentationEnergy.lean

open scoped BigOperators
namespace Erdos52.RSFresh

theorem difference_representation_energy (A X Y : Finset ℝ) (T : ℕ)
    (hA : ∀ a ∈ A, a ≠ 0) (hrep : ∀ a ∈ A, T ≤ diffCount X Y a) :
    (mulEnergy A : ℝ)*(T : ℝ)^4 ≤
      8193*(X.card : ℝ)^3*(Y.card : ℝ)^3*(logBudget X.card : ℝ) := by
  classical
  have hl := representation_energy_lift A X Y T hA hrep
  have ht := rayCollision_sum_bound X Y
  have hm := mixed_collinear_bound X Y (rayLines X Y)
    (fun l hl => rayLines_slope X Y hl) (fun l hl => rayLines_rich X Y hl)
  have hlr : (mulEnergy A : ℝ)*(T : ℝ)^4 ≤
      (X.card : ℝ)*Y.card*(∑ c ∈ Y ×ˢ X, (rayCollision X Y c : ℝ)) := by
    exact_mod_cast hl
  have htr : (∑ c ∈ Y ×ˢ X, (rayCollision X Y c : ℝ)) ≤
      (X.card : ℝ)^2*(Y.card : ℝ)^2 +
        ∑ l ∈ rayLines X Y, ((linePoints X Y l).card : ℝ)^2*(linePoints Y X l).card := by
    exact_mod_cast ht
  have hL : (1 : ℝ) ≤ logBudget X.card := by
    exact_mod_cast (show 1 ≤ logBudget X.card from logBudget_pos X.card)
  have hbase : (X.card : ℝ)^2*(Y.card : ℝ)^2 ≤
      (X.card : ℝ)^2*(Y.card : ℝ)^2*(logBudget X.card : ℝ) := by
    exact le_mul_of_one_le_right (by positivity) hL
  have hs : (∑ c ∈ Y ×ˢ X, (rayCollision X Y c : ℝ)) ≤
      8193*(X.card : ℝ)^2*(Y.card : ℝ)^2*(logBudget X.card : ℝ) := by nlinarith
  calc
    (mulEnergy A : ℝ)*(T : ℝ)^4 ≤
      (X.card : ℝ)*Y.card*(∑ c ∈ Y ×ˢ X, (rayCollision X Y c : ℝ)) := hlr
    _ ≤ (X.card : ℝ)*Y.card*(8193*(X.card : ℝ)^2*(Y.card : ℝ)^2*(logBudget X.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end Erdos52.RSFresh

-- END RSProof/DifferenceRepresentationEnergy.lean

-- BEGIN RSProof/UniformRepresentationEnergy.lean

namespace Erdos52.RSFresh

theorem logBudget_double (n : ℕ) : logBudget (2*n) ≤ 2*logBudget n := by
  by_cases hn : n=0
  · subst n
    norm_num [logBudget]
  · unfold logBudget
    rw [Nat.mul_comm 2 n,Nat.log_mul_base (by norm_num : 1 < (2 : ℕ)) hn]
    omega

theorem uniform_difference_energy (A X Y : Finset ℝ) (T τ n : ℕ)
    (hτ : τ ≤ n) (hX : X.card ≤ 2*τ) (hY : Y.card ≤ 2*τ)
    (hA : ∀ a ∈ A, a ≠ 0) (hrep : ∀ a ∈ A, T ≤ diffCount X Y a) :
    (mulEnergy A : ℝ)*(T : ℝ)^4 ≤ 1048704*(τ : ℝ)^6*(logBudget n : ℝ) := by
  have he := difference_representation_energy A X Y T hA hrep
  have hx : (X.card : ℝ) ≤ 2*(τ : ℝ) := by exact_mod_cast hX
  have hy : (Y.card : ℝ) ≤ 2*(τ : ℝ) := by exact_mod_cast hY
  have hl : (logBudget X.card : ℝ) ≤ 2*(logBudget n : ℝ) := by
    have hh := (logBudget_mono (hX.trans (Nat.mul_le_mul_left 2 hτ))).trans (logBudget_double n)
    exact_mod_cast hh
  calc
    (mulEnergy A : ℝ)*(T : ℝ)^4 ≤ 8193*(X.card : ℝ)^3*(Y.card : ℝ)^3*(logBudget X.card : ℝ) := he
    _ ≤ 8193*(2*(τ : ℝ))^3*(2*(τ : ℝ))^3*(2*(logBudget n : ℝ)) := by gcongr
    _ = 1048704*(τ : ℝ)^6*(logBudget n : ℝ) := by ring

end Erdos52.RSFresh

-- END RSProof/UniformRepresentationEnergy.lean

-- BEGIN RSProof/GoodProductActual.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem good_slope_product (A S : Finset ℝ) (hA : Positive A) (b τ : ℕ)
    (hb : 0 < b) (hτ : 0 < τ) (hτn : τ ≤ A.card)
    (hupper : ∀ s ∈ S, (slopeFiber A s).card ≤ 2*τ)
    (hE : (mulEnergy A : ℝ) ≤ 4*(logBudget A.card : ℝ)*(S.card : ℝ)*(τ : ℝ)^2)
    {s : ℝ} (hs : s ∈ goodSlopes A S ((τ : ℝ)^2/(2*(b : ℝ)^2))) :
    (A.card : ℝ)^4 ≤ (1024*1048704 : ℝ)*((A*slopeFiber A s).card : ℝ)^2*
      (S.card : ℝ)*(b : ℝ)^8*(logBudget A.card : ℝ)^6 := by
  apply good_slope_product_bound A S hA b τ hb hτ 1048704 (by norm_num) hupper hE _ hs
  intro X Y C t hC ht hX hY hX0 hY0 hC0 hrep
  exact uniform_difference_energy C X Y t τ A.card hτn hX hY hC0 hrep

end Erdos52.RSFresh

-- END RSProof/GoodProductActual.lean

-- BEGIN RSProof/ProductRatioLift.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem positive_product {A B : Finset ℝ} (hA : Positive A) (hB : Positive B) : Positive (A*B) := by
  classical
  intro z hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hz
  exact mul_pos (hA a ha) (hB b hb)

theorem card_le_product (A : Finset ℝ) (hA : Positive A) : A.card ≤ (A*A).card := by
  classical
  by_cases hn : A.Nonempty
  · obtain ⟨a,ha⟩ := hn
    apply Finset.card_le_card_of_injOn (fun x : ℝ => x*a)
    · intro x hx
      exact Finset.mul_mem_mul hx ha
    · intro x hx y hy he
      exact mul_right_cancel₀ (ne_of_gt (hA a ha)) he
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

theorem product_fiber_ratio_lift (A : Finset ℝ) (hA : Positive A) (s : ℝ) :
    (A*slopeFiber A s).card ≤ ratioCount (A*A) (A*A) s := by
  classical
  apply Finset.card_le_card_of_injOn (fun z : ℝ => (s*z,z))
  · intro z hz
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hz
    obtain ⟨hbA,hsb⟩ := Finset.mem_filter.mp hb
    have hab : a*b ≠ 0 := ne_of_gt (mul_pos (hA a ha) (hA b hbA))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,Finset.mul_mem_mul ha hbA⟩,?_⟩
    · have he : s*(a*b)=a*(s*b) := by ring
      change s*(a*b) ∈ A*A
      rw [he]
      exact Finset.mul_mem_mul ha hsb
    · exact (div_eq_iff hab).mpr rfl
  · intro x hx y hy he
    exact congrArg Prod.snd he

end Erdos52.RSFresh

-- END RSProof/ProductRatioLift.lean

-- BEGIN RSProof/SlopeSlice.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def slopeSlice (A G : Finset ℝ) (a : ℝ) : Finset ℝ := by
  classical
  exact G.filter (fun t => a ∈ slopeFiber A t)

theorem slope_slice_total (A G : Finset ℝ) :
    (∑ a ∈ A, (slopeSlice A G a).card) = ∑ t ∈ G, (slopeFiber A t).card := by
  classical
  simp only [slopeSlice,slopeFiber,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.mem_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ha,true_and]

theorem exists_large_slope_slice (A G : Finset ℝ) (hA : A.Nonempty) (τ : ℕ)
    (hτ : ∀ t ∈ G, τ ≤ (slopeFiber A t).card) :
    ∃ a ∈ A, G.card*τ ≤ A.card*(slopeSlice A G a).card := by
  classical
  obtain ⟨a,ha,hmax⟩ := A.exists_max_image (fun a => (slopeSlice A G a).card) hA
  refine ⟨a,ha,?_⟩
  calc
    G.card*τ = ∑ _t ∈ G, τ := by simp
    _ ≤ ∑ t ∈ G, (slopeFiber A t).card := Finset.sum_le_sum hτ
    _ = ∑ x ∈ A, (slopeSlice A G x).card := (slope_slice_total A G).symm
    _ ≤ ∑ _x ∈ A, (slopeSlice A G a).card := Finset.sum_le_sum hmax
    _ = A.card*(slopeSlice A G a).card := by simp

theorem slopeSlice_subset (A G : Finset ℝ) (a : ℝ) : slopeSlice A G a ⊆ G := by
  classical
  exact Finset.filter_subset _ _

theorem slopeSlice_positive (A G : Finset ℝ) (hA : Positive A) (a : ℝ) (ha : a ∈ A) :
    Positive (slopeSlice A G a) := by
  classical
  intro t ht
  have hta := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).2).2
  have ha0 := hA a ha
  have ht0 := hA (t*a) hta
  nlinarith

theorem slopeSlice_sum_card (A G : Finset ℝ) (a : ℝ) (ha : a ≠ 0) :
    (slopeSlice A G a + slopeSlice A G a).card ≤ (A+A).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun x : ℝ => x*a)
  · intro x hx
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hx
    have huA := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).2).2
    have hvA := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).2
    change (u+v)*a ∈ A+A
    rw [add_mul]
    exact Finset.add_mem_add huA hvA
  · intro x hx y hy he
    exact mul_right_cancel₀ ha he

end Erdos52.RSFresh

-- END RSProof/SlopeSlice.lean

-- BEGIN RSProof/SlopeSliceCard.lean

namespace Erdos52.RSFresh

theorem slopeSlice_card_le (A G : Finset ℝ) (a : ℝ) (ha : a ≠ 0) :
    (slopeSlice A G a).card ≤ A.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun t : ℝ => t*a)
  · intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).2).2
  · intro x hx y hy he
    exact mul_right_cancel₀ ha he

end Erdos52.RSFresh

-- END RSProof/SlopeSliceCard.lean

-- BEGIN RSProof/RebunchSize.lean

namespace Erdos52.RSFresh

noncomputable def rebunchSize (u w : ℝ) : ℕ := Nat.ceil (32*u^2/w)+1

theorem rebunchSize_pos (u w : ℝ) : 0 < rebunchSize u w := by
  unfold rebunchSize
  omega

theorem rebunchSize_bounds (u w : ℝ) (hw : 0 < w) (hwu : w ≤ 2*u^2) :
    16*u^2 < (rebunchSize u w : ℝ)*w ∧
      (rebunchSize u w : ℝ)*w ≤ 36*u^2 := by
  have hu : 0 < u^2 := by linarith
  have hr : 0 ≤ 32*u^2/w := by positivity
  have hlo := Nat.le_ceil (32*u^2/w)
  have hhi := Nat.ceil_lt_add_one hr
  have hc : (rebunchSize u w : ℝ) = (Nat.ceil (32*u^2/w) : ℝ)+1 := by
    simp only [rebunchSize,Nat.cast_add,Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hlo hw.le
  have hmhi := mul_lt_mul_of_pos_right hhi hw
  have he : (32*u^2/w)*w=32*u^2 := div_mul_cancel₀ _ (ne_of_gt hw)
  rw [he] at hmul
  rw [add_mul,he,one_mul] at hmhi
  constructor <;> rw [hc,add_mul,one_mul] <;> nlinarith

end Erdos52.RSFresh

-- END RSProof/RebunchSize.lean

-- BEGIN RSProof/RebunchGuard.lean

namespace Erdos52.RSFresh

theorem rebunch_feasible (n u v L s τ b : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hL : 0 < L) (hs : 0 < s) (hτ : 0 < τ)
    (hτn : τ ≤ n)
    (henergy : n^4 ≤ 4*L*v*s*τ^2)
    (hb : b*(s*τ^2) ≤ 36*u^2)
    (hguard : 4608*u^2*v^2*L^2 ≤ n^6) : 8*b ≤ s := by
  by_contra hnot
  have hsb : s < 8*b := lt_of_not_ge hnot
  have hsw : s*(s*τ^2) < 288*u^2 := by
    have hm := mul_lt_mul_of_pos_right hsb (by positivity : 0 < s*τ^2)
    nlinarith
  have he := pow_le_pow_left₀ (by positivity : 0 ≤ n^4) henergy 2
  have ht := pow_le_pow_left₀ hτ.le hτn 2
  have hupper : n^8 ≤ 16*L^2*v^2*(s*(s*τ^2))*n^2 := by
    calc
      n^8 = (n^4)^2 := by ring
      _ ≤ (4*L*v*s*τ^2)^2 := he
      _ = (16*L^2*v^2*(s*(s*τ^2)))*τ^2 := by ring
      _ ≤ (16*L^2*v^2*(s*(s*τ^2)))*n^2 :=
        mul_le_mul_of_nonneg_left ht (by positivity)
  have hstrict : 16*L^2*v^2*(s*(s*τ^2))*n^2 < n^8 := by
    calc
      16*L^2*v^2*(s*(s*τ^2))*n^2 = (16*L^2*v^2*n^2)*(s*(s*τ^2)) := by ring
      _ < (16*L^2*v^2*n^2)*(288*u^2) :=
        mul_lt_mul_of_pos_left hsw (by positivity)
      _ = (4608*u^2*v^2*L^2)*n^2 := by ring
      _ ≤ n^6*n^2 := mul_le_mul_of_nonneg_right hguard (by positivity)
      _ = n^8 := by ring
  exact (not_lt_of_ge hupper) hstrict

end Erdos52.RSFresh

-- END RSProof/RebunchGuard.lean

-- BEGIN RSProof/SumProductStructure.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

theorem exists_sum_product_structure (A : Finset ℝ) (hA : Positive A) (hn : A.Nonempty)
    (hguard : 4608*((A+A).card : ℝ)^2*((A*A).card : ℝ)^2*(logBudget A.card : ℝ)^2 ≤ (A.card : ℝ)^6) :
    ∃ s τ b T : ℕ, ∃ B : Finset ℝ,
      0 < s ∧ 0 < τ ∧ 0 < b ∧ 0 < T ∧ s ≤ A.card^2 ∧ τ ≤ A.card ∧
      (A.card : ℝ)^4 ≤ 4*(logBudget A.card : ℝ)*((A*A).card : ℝ)*(s : ℝ)*(τ : ℝ)^2 ∧
      (b : ℝ)*((s : ℝ)*(τ : ℝ)^2) ≤ 36*((A+A).card : ℝ)^2 ∧
      s*τ ≤ 2*A.card*B.card ∧ B.card ≤ A.card ∧ B.Nonempty ∧ Positive B ∧
      (B+B).card ≤ (A+A).card ∧
      (∀ z ∈ B, T ≤ ratioCount (A*A) (A*A) z) ∧
      (A.card : ℝ)^4 ≤ (1024*1048704 : ℝ)*(T : ℝ)^2*(s : ℝ)*(b : ℝ)^8*(logBudget A.card : ℝ)^6 := by
  classical
  obtain ⟨S,hS,hSn,τ,hτ,hτn,hfib,hE⟩ := exists_energy_slope_class A hA hn
  let w := (S.card : ℝ)*(τ : ℝ)^2
  let b := rebunchSize ((A+A).card : ℝ) w
  have hn0 : 0 < (A.card : ℝ) := by exact_mod_cast hn.card_pos
  have hs0 : 0 < (S.card : ℝ) := by exact_mod_cast hSn.card_pos
  have ht0 : 0 < (τ : ℝ) := by exact_mod_cast hτ
  have hw : 0 < w := by dsimp [w]; positivity
  have hwupper : w ≤ 2*((A+A).card : ℝ)^2 := by
    dsimp only [w]
    exact_mod_cast slope_class_weight A hA S τ (fun z hz => (hfib z hz).1)
  have hb := rebunchSize_bounds ((A+A).card : ℝ) w hw hwupper
  have hb0 : 0 < b := rebunchSize_pos _ _
  have he0 := positive_mulEnergy_lower A hA
  have heR : (A.card : ℝ)^4 ≤ 4*(logBudget A.card : ℝ)*((A*A).card : ℝ)*(S.card : ℝ)*(τ : ℝ)^2 := by
    have hh : A.card^4 ≤ (A*A).card*(4*logBudget A.card*S.card*τ^2) :=
      he0.trans (Nat.mul_le_mul_left _ hE)
    exact_mod_cast (by nlinarith [hh] : A.card^4 ≤ 4*logBudget A.card*(A*A).card*S.card*τ^2)
  have hv0 : 0 < ((A*A).card : ℝ) := by
    have hh := (hn.card_pos).trans_le (card_le_product A hA)
    exact_mod_cast hh
  have hL0 : 0 < (logBudget A.card : ℝ) := by exact_mod_cast logBudget_pos A.card
  have hfeas : 8*b ≤ S.card := by
    have hh := rebunch_feasible (A.card : ℝ) ((A+A).card : ℝ) ((A*A).card : ℝ)
      (logBudget A.card : ℝ) (S.card : ℝ) (τ : ℝ) (b : ℝ)
      hn0 hv0 hL0 hs0 ht0 (by exact_mod_cast hτn) heR hb.2 hguard
    exact_mod_cast hh
  let G := goodSlopes A S ((τ : ℝ)^2/(2*(b : ℝ)^2))
  have hGcard : S.card < 2*G.card := many_good_slopes A S hA b τ hb0 hfeas
    (fun z hz => (hfib z hz).1) (by dsimp [w] at hb; nlinarith [hb.1])
  have hGn : G.Nonempty := Finset.card_pos.mp (by have := hSn.card_pos; omega)
  have hGs : G ⊆ S := Finset.filter_subset _ _
  obtain ⟨z,hz,hmin⟩ := G.exists_min_image (fun z => (A*slopeFiber A z).card) hGn
  let T := (A*slopeFiber A z).card
  have hT : 0 < T := by
    have hf : (slopeFiber A z).Nonempty := Finset.card_pos.mp ((hτ).trans_le (hfib z (hGs hz)).1)
    obtain ⟨a,ha⟩ := hn
    obtain ⟨c,hc⟩ := hf
    exact Finset.card_pos.mpr ⟨a*c,Finset.mul_mem_mul ha hc⟩
  obtain ⟨a,ha,hslice⟩ := exists_large_slope_slice A G hn τ
    (fun z hz => (hfib z (hGs hz)).1)
  let B := slopeSlice A G a
  have ha0 : a ≠ 0 := ne_of_gt (hA a ha)
  have hBcard : S.card*τ ≤ 2*A.card*B.card := by
    have hh := Nat.mul_le_mul_right τ hGcard.le
    nlinarith
  have hBn : B.Nonempty := Finset.card_pos.mp (by
    have hspos := hSn.card_pos
    have hmul : 0 < S.card*τ := Nat.mul_pos hspos hτ
    by_contra h
    have hz : B.card=0 := by omega
    rw [hz,mul_zero] at hBcard
    omega)
  have hsbound : S.card ≤ A.card^2 := by
    have hh := (Finset.card_le_card hS).trans (Finset.card_div_le (s := A) (t := A))
    simpa only [pow_two] using hh
  refine ⟨S.card,τ,b,T,B,hSn.card_pos,hτ,hb0,hT,hsbound,hτn,heR,hb.2,
    hBcard,slopeSlice_card_le A G a ha0,hBn,slopeSlice_positive A G hA a ha,
    slopeSlice_sum_card A G a ha0,?_,?_⟩
  · intro t ht
    exact (hmin t (slopeSlice_subset A G a ht)).trans (product_fiber_ratio_lift A hA t)
  · exact good_slope_product A S hA b τ hb0 hτ hτn
      (fun t ht => (hfib t ht).2.le) (by exact_mod_cast hE) hz

end Erdos52.RSFresh

-- END RSProof/SumProductStructure.lean

-- BEGIN RSProof/FewProductsAlgebra.lean

namespace Erdos52.RSFresh

def cubicConstant : ℝ := 82944
def fewProductsConstant : ℝ := 64^6*cubicConstant^11*8^7

 theorem few_products_core_power (N d delta T q S L a b c R : ℝ)
    (hN : 0<N) (hd : 0<d) (_hdelta : 0≤delta) (hT : 0≤T) (_hq : 0≤q)
    (_hS : 0≤S) (hL : 0≤L) (ha0 : 0≤a) (_hb0 : 0≤b) (hc0 : 0≤c) (_hR0 : 0≤R)
    (hmain : N^4*d^2*delta^2 ≤ 64*L*a*S*R)
    (hR : R^6 ≤ (N*d)^3*b*c^2)
    (ha : a*T^3 ≤ cubicConstant*q^4*N^2*L)
    (hb : b*T^3 ≤ cubicConstant*q^4*d^2*L)
    (hc : c*T^3 ≤ cubicConstant*q^4*S^2*L) :
    N^9*d^7*delta^12*T^27 ≤ 64^6*cubicConstant^9*q^36*S^10*L^15 := by
  have hC : 0≤cubicConstant := by norm_num [cubicConstant]
  have hr : R^6*T^9 ≤ cubicConstant^3*q^12*N^3*d^5*S^4*L^3 := by
    calc
      _ ≤ ((N*d)^3*b*c^2)*T^9 := mul_le_mul_of_nonneg_right hR (pow_nonneg hT _)
      _ = (N*d)^3*(b*T^3)*(c*T^3)^2 := by ring
      _ ≤ (N*d)^3*(cubicConstant*q^4*d^2*L)*(cubicConstant*q^4*S^2*L)^2 := by
        gcongr
      _ = _ := by ring
  apply le_of_mul_le_mul_left (a := N^15*d^5) _ (by positivity)
  calc
    _ = (N^4*d^2*delta^2)^6*T^27 := by ring
    _ ≤ (64*L*a*S*R)^6*T^27 := by gcongr
    _ = 64^6*L^6*(a*T^3)^6*S^6*(R^6*T^9) := by ring
    _ ≤ 64^6*L^6*(cubicConstant*q^4*N^2*L)^6*S^6*
        (cubicConstant^3*q^12*N^3*d^5*S^4*L^3) := by gcongr
    _ = _ := by ring

 theorem few_products_eliminate (N d delta T q S L E : ℝ)
    (hN : 0<N) (_hd : 0<d) (hdelta : 0≤delta) (hT : 0≤T) (_hq : 0≤q)
    (hS : 0≤S) (hL : 0≤L) (hE : 0≤E)
    (hcore : N^9*d^7*delta^12*T^27 ≤ 64^6*cubicConstant^9*q^36*S^10*L^15)
    (hdeltaE : E*delta*T^3 ≤ cubicConstant*q^4*N^2*L)
    (hloc : E ≤ 8*L*d*delta^2) (henergy : N^4 ≤ S*E) :
    N^41*T^33 ≤ fewProductsConstant*q^44*S^19*L^24 := by
  have hC : 0≤cubicConstant := by norm_num [cubicConstant]
  have hmid : N^5*(d*delta^2)^7*T^33*E^2 ≤ 64^6*cubicConstant^11*q^44*S^10*L^17 := by
    apply le_of_mul_le_mul_left (a := N^4) _ (pow_pos hN _)
    calc
      _ = (N^9*d^7*delta^12*T^27)*(E*delta*T^3)^2 := by ring
      _ ≤ (64^6*cubicConstant^9*q^36*S^10*L^15)*(cubicConstant*q^4*N^2*L)^2 := by gcongr
      _ = _ := by ring
  have he : N^5*E^9*T^33 ≤ fewProductsConstant*q^44*S^10*L^24 := by
    calc
      _ = N^5*E^7*T^33*E^2 := by ring
      _ ≤ N^5*(8*L*d*delta^2)^7*T^33*E^2 := by gcongr
      _ = (8*L)^7*(N^5*(d*delta^2)^7*T^33*E^2) := by ring
      _ ≤ (8*L)^7*(64^6*cubicConstant^11*q^44*S^10*L^17) :=
        mul_le_mul_of_nonneg_left hmid (pow_nonneg (mul_nonneg (by norm_num) hL) _)
      _ = _ := by unfold fewProductsConstant; ring
  calc
    _ = N^5*(N^4)^9*T^33 := by ring
    _ ≤ N^5*(S*E)^9*T^33 := by gcongr
    _ = S^9*(N^5*E^9*T^33) := by ring
    _ ≤ S^9*(fewProductsConstant*q^44*S^10*L^24) := mul_le_mul_of_nonneg_left he (pow_nonneg hS _)
    _ = _ := by ring

end Erdos52.RSFresh

-- END RSProof/FewProductsAlgebra.lean

-- BEGIN RSProof/IncidenceCounting.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem card_filter_product {α β : Type*} (S : Finset α) (T : Finset β)
    (R : α → β → Prop) [DecidablePred (fun p : α × β => R p.1 p.2)]
    [∀ a, DecidablePred (R a)] :
    ((S ×ˢ T).filter (fun p => R p.1 p.2)).card = ∑ a ∈ S, (T.filter (R a)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

noncomputable def incidenceSet (A B : Finset ℝ) (L : Finset (ℝ × ℝ)) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) := by
  classical
  exact (L ×ˢ (A ×ˢ B)).filter (fun z => OnLine z.1 z.2)

 theorem incidenceSet_card (A B : Finset ℝ) (L : Finset (ℝ × ℝ)) :
    (incidenceSet A B L).card = incidenceCount A B L := by
  classical
  exact card_filter_product L (A ×ˢ B) OnLine

noncomputable def differencePairs (A B D : Finset ℝ) :=
  (A ×ˢ B).filter (fun p => p.1-p.2 ∈ D)

 theorem differencePairs_card (A B D : Finset ℝ) :
    (differencePairs A B D).card = ∑ d ∈ D, diffCount A B d := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ B) D (fun p : ℝ × ℝ => p.1-p.2)
  exact h.symm

noncomputable def ratioLines (P D : Finset ℝ) : Finset (ℝ × ℝ) :=
  (P ×ˢ D).image (fun z => (z.1⁻¹,-z.2))

 theorem ratioLines_card (P D : Finset ℝ) : (ratioLines P D).card = P.card*D.card := by
  classical
  rw [ratioLines,Finset.card_image_of_injective,Finset.card_product]
  intro p q h
  apply Prod.ext
  · exact inv_injective (congrArg (fun z : ℝ × ℝ => z.1) h)
  · exact neg_injective (congrArg (fun z : ℝ × ℝ => z.2) h)

 theorem ratioLines_nonzero (P D : Finset ℝ) (hP : ∀ p ∈ P, p≠0) :
    ∀ l ∈ ratioLines P D, l.1≠0 := by
  intro l hl
  obtain ⟨⟨p,d⟩,hpd,rfl⟩ := Finset.mem_image.mp hl
  exact inv_ne_zero (hP p (Finset.mem_product.mp hpd).1)

end Erdos52.RSFresh

-- END RSProof/IncidenceCounting.lean

-- BEGIN RSProof/RatioIncidence.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem ratio_incidence_lower (A B D P : Finset ℝ) (T : ℕ)
    (_hP : ∀ p ∈ P, p≠0) (hT : ∀ a ∈ A, T ≤ ratioCount P P a) :
    T*(differencePairs A B D).card ≤ incidenceCount P B (ratioLines P D) := by
  classical
  let S := differencePairs A B D
  let Q := (S ×ˢ (P ×ˢ P)).filter (fun z => z.2.1/z.2.2=z.1.1)
  have hcard : T*S.card ≤ Q.card := by
    dsimp only [Q]
    rw [card_filter_product S (P ×ˢ P) (fun ab pq => pq.1/pq.2=ab.1)]
    calc
      _ = ∑ _z ∈ S, T := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z hz
        exact hT z.1 (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  let F : ((ℝ × ℝ) × (ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun z => ((z.2.2⁻¹,-(z.1.1-z.1.2)),(z.2.1,z.1.2))
  have hmap : ∀ z ∈ Q, F z ∈ incidenceSet P B (ratioLines P D) := by
    intro z hz
    have hz0 := Finset.mem_filter.mp hz
    have hab := Finset.mem_filter.mp (Finset.mem_product.mp hz0.1).1
    have hpq := Finset.mem_product.mp (Finset.mem_product.mp hz0.1).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_image.mpr ⟨(z.2.2,z.1.1-z.1.2),?_,rfl⟩,?_⟩
      · exact Finset.mem_product.mpr ⟨hpq.2,hab.2⟩
      · exact Finset.mem_product.mpr ⟨hpq.1,(Finset.mem_product.mp hab.1).2⟩
    · dsimp [F,OnLine]
      rw [div_eq_mul_inv] at hz0
      nlinarith [hz0.2]
  have hinj : Set.InjOn F Q := by
    intro z hz w hw he
    have hz0 := (Finset.mem_filter.mp hz).2
    have hw0 := (Finset.mem_filter.mp hw).2
    have hq : z.2.2=w.2.2 := inv_injective (congrArg (fun a : (ℝ×ℝ)×(ℝ×ℝ) => a.1.1) he)
    have hp := congrArg (fun a : (ℝ×ℝ)×(ℝ×ℝ) => a.2.1) he
    change z.2.1=w.2.1 at hp
    have hb := congrArg (fun a : (ℝ×ℝ)×(ℝ×ℝ) => a.2.2) he
    change z.1.2=w.1.2 at hb
    have ha : z.1.1=w.1.1 := by rw [← hz0,← hw0,hp,hq]
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hp hq)
  have hc := Finset.card_le_card_of_injOn F hmap hinj
  rw [incidenceSet_card] at hc
  exact hcard.trans hc

end Erdos52.RSFresh

-- END RSProof/RatioIncidence.lean

-- BEGIN RSProof/RatioRichDifferences.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem ratio_rich_differences (A B D P : Finset ℝ) (k T : ℕ)
    (hP : ∀ p ∈ P, p≠0) (hAP : A.card ≤ P.card)
    (hT : ∀ a ∈ A, T ≤ ratioCount P P a) (hD : D ⊆ A-B)
    (hk : ∀ d ∈ D, k ≤ diffCount A B d) :
    (D.card:ℝ)*(k*T:ℕ)^3 ≤ 10368*(P.card:ℝ)^4*(B.card:ℝ)^2 := by
  classical
  by_cases hd : D.card=0
  · simp only [hd,Nat.cast_zero,zero_mul]
    positivity
  have hd0 : (0:ℝ)<D.card := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hcard : D.card ≤ P.card*B.card :=
    (Finset.card_le_card hD).trans (Finset.card_sub_le.trans (Nat.mul_le_mul_right B.card hAP))
  have hb0 : 1 ≤ B.card := by nlinarith [Nat.pos_of_ne_zero hd]
  have hcount : k*D.card ≤ (differencePairs A B D).card := by
    rw [differencePairs_card]
    calc
      _ = ∑ _d ∈ D, k := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hk
  have hlo : k*T*D.card ≤ incidenceCount P B (ratioLines P D) := by
    have hh := (Nat.mul_le_mul_left T hcount).trans (ratio_incidence_lower A B D P T hP hT)
    nlinarith
  have hlor : (k*T:ℕ)*(D.card:ℝ) ≤ incidenceCount P B (ratioLines P D) := by exact_mod_cast hlo
  rcases incidence_cubic P B (ratioLines P D) (ratioLines_nonzero P D hP) with hlin | hcub
  · rw [ratioLines_card] at hlin
    have hu : (k*T:ℕ)*(D.card:ℝ) ≤ 8*(P.card:ℝ)*D.card := by exact_mod_cast (by simpa [Nat.mul_assoc] using hlo.trans hlin)
    have hu' : (k*T:ℕ) ≤ 8*(P.card:ℝ) := le_of_mul_le_mul_right hu hd0
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(k*T:ℕ)) hu' 3
    have hd' : (D.card:ℝ) ≤ (P.card:ℝ)*B.card := by exact_mod_cast hcard
    have hb' : (1:ℝ) ≤ B.card := by exact_mod_cast hb0
    calc
      _ ≤ (P.card:ℝ)*B.card*(8*(P.card:ℝ))^3 := mul_le_mul hd' hp (by positivity) (by positivity)
      _ = 512*(P.card:ℝ)^4*(B.card:ℝ) := by ring
      _ ≤ 512*(P.card:ℝ)^4*(B.card:ℝ)^2 :=
        mul_le_mul_of_nonneg_left (by nlinarith : (B.card:ℝ)≤(B.card:ℝ)^2) (by positivity)
      _ ≤ _ := by nlinarith [show 0≤(P.card:ℝ)^4*(B.card:ℝ)^2 by positivity]
  · rw [ratioLines_card] at hcub
    push_cast at hcub
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(k*T:ℕ)*(D.card:ℝ)) hlor 3
    apply le_of_mul_le_mul_right (a := (D.card:ℝ)^2) _ (sq_pos_of_pos hd0)
    calc
      _ = ((k*T:ℕ)*(D.card:ℝ))^3 := by ring
      _ ≤ _ := hp.trans hcub
      _ = _ := by ring

end Erdos52.RSFresh

-- END RSProof/RatioRichDifferences.lean

-- BEGIN RSProof/CubicEnergy.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def energy3 (A B : Finset ℝ) : ℕ := ∑ d ∈ A-B, (diffCount A B d)^3

 theorem diffCount_pos {A B : Finset ℝ} {d : ℝ} (hd : d ∈ A-B) : 0 < diffCount A B d := by
  classical
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hd
  exact Finset.card_pos.mpr ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩⟩

 theorem dyadic_cube_partition {α : Type*} (S : Finset α) (f : α → ℕ) (n : ℕ)
    (hf : ∀ x ∈ S, f x ≤ n) :
    ∑ j ∈ Finset.range (logBudget n), ∑ x ∈ dyadicClass S f j, (f x)^3 =
      ∑ x ∈ S, (f x)^3 := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro x hx
  apply Finset.mem_range.mpr
  have hh := Nat.log_mono_right (b := 2) (hf x hx)
  unfold logBudget
  omega

 theorem ratio_cubic_energy (A B P : Finset ℝ) (T : ℕ)
    (hP : ∀ p ∈ P, p≠0) (hAP : A.card ≤ P.card)
    (hT : ∀ a ∈ A, T ≤ ratioCount P P a) :
    (energy3 A B : ℝ)*(T:ℝ)^3 ≤
      82944*(P.card:ℝ)^4*(B.card:ℝ)^2*logBudget A.card := by
  classical
  have hc (j : ℕ) :
      ((∑ d ∈ dyadicClass (A-B) (diffCount A B) j, (diffCount A B d)^3 : ℕ):ℝ)*(T:ℝ)^3 ≤
        82944*(P.card:ℝ)^4*(B.card:ℝ)^2 := by
    let D := dyadicClass (A-B) (diffCount A B) j
    have hr := ratio_rich_differences A B D P (2^j) T hP hAP hT (Finset.filter_subset _ _)
      (fun d hd => (dyadicClass_bounds (A-B) (diffCount A B) (fun _ h => diffCount_pos h) j hd).1)
    have hb : (∑ d ∈ D, (diffCount A B d)^3) ≤ 8*D.card*(2^j)^3 := by
      calc
        _ ≤ ∑ _d ∈ D, 8*(2^j)^3 := by
          apply Finset.sum_le_sum
          intro d hd
          have h := (dyadicClass_bounds (A-B) (diffCount A B) (fun _ h => diffCount_pos h) j hd).2.le
          have hp := Nat.pow_le_pow_left h 3
          nlinarith
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; ring
    have hbr : ((∑ d ∈ D, (diffCount A B d)^3 : ℕ):ℝ) ≤ 8*(D.card:ℝ)*((2:ℝ)^j)^3 := by exact_mod_cast hb
    push_cast at hr
    have hh := mul_le_mul_of_nonneg_right hbr (by positivity : 0≤(T:ℝ)^3)
    change ((∑ d ∈ D, (diffCount A B d)^3 : ℕ):ℝ)*(T:ℝ)^3 ≤ _
    nlinarith
  have hp := dyadic_cube_partition (A-B) (diffCount A B) A.card (fun d _ => diffCount_le_left A B d)
  change ((∑ d ∈ A-B, (diffCount A B d)^3 : ℕ):ℝ)*(T:ℝ)^3 ≤ _
  rw [← hp, Nat.cast_sum, Finset.sum_mul]
  calc
    _ ≤ ∑ _j ∈ Finset.range (logBudget A.card), 82944*(P.card:ℝ)^4*(B.card:ℝ)^2 :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = _ := by simp; ring

end Erdos52.RSFresh

-- END RSProof/CubicEnergy.lean

-- BEGIN RSProof/PopularRows.lean

open scoped BigOperators
namespace Erdos52.RSFresh

noncomputable def richRows {α : Type*} (A : Finset α) (bad : α → ℕ) : Finset α := by
  classical
  exact A.filter (fun a => 2 * bad a ≤ A.card)

theorem richRows_subset {α : Type*} (A : Finset α) (bad : α → ℕ) :
    richRows A bad ⊆ A := by
  classical
  exact Finset.filter_subset _ _

theorem richRows_retention {α : Type*} (A : Finset α) (bad : α → ℕ)
    (ε : ℝ)
    (hsum : (∑ a ∈ A, (bad a : ℝ)) ≤ ε * (A.card : ℝ)^2) :
    (A.card : ℝ) ≤ (richRows A bad).card + 2 * ε * A.card := by
  classical
  by_cases hA : A.card = 0
  · simp [richRows, Finset.card_eq_zero.mp hA]
  have hn : 0 < (A.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hA
  let B := A \ richRows A bad
  have hB : (B.card : ℝ) * (A.card : ℝ) ≤ 2 * ∑ a ∈ A, (bad a : ℝ) := by
    calc
      (B.card : ℝ) * (A.card : ℝ) = ∑ _a ∈ B, (A.card : ℝ) := by simp
      _ ≤ ∑ a ∈ B, 2 * (bad a : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        have hmem := Finset.mem_sdiff.mp ha
        have hbad : ¬ 2 * bad a ≤ A.card := by
          intro h
          exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1, h⟩)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hbad))
      _ = 2 * ∑ a ∈ B, (bad a : ℝ) := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ a ∈ A, (bad a : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.sdiff_subset
        · intros; positivity
  have hcard : B.card + (richRows A bad).card = A.card := by
    exact Finset.card_sdiff_add_card_eq_card (richRows_subset A bad)
  have hc : (B.card : ℝ) + ((richRows A bad).card : ℝ) = A.card := by
    exact_mod_cast hcard
  nlinarith

end Erdos52.RSFresh

-- END RSProof/PopularRows.lean

-- BEGIN RSProof/PopularSums.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def popularSums (A : Finset ℝ) (ε : ℝ) : Finset ℝ := by
  classical
  exact (A+A).filter (fun s => ε * (A.card : ℝ)^2 / (A+A).card ≤ sumCount A A s)

noncomputable def unpopularCount (A : Finset ℝ) (ε : ℝ) (a : ℝ) : ℕ := by
  classical
  exact (A.filter (fun b => a+b ∉ popularSums A ε)).card

theorem unpopular_total (A : Finset ℝ) (ε : ℝ) :
    ∑ a ∈ A, unpopularCount A ε a =
      ((A ×ˢ A).filter (fun p => p.1+p.2 ∉ popularSums A ε)).card := by
  classical
  simp only [unpopularCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]

theorem unpopular_by_sum (A : Finset ℝ) (ε : ℝ) :
    ∑ a ∈ A, unpopularCount A ε a =
      ∑ s ∈ (A+A) \ popularSums A ε, sumCount A A s := by
  classical
  rw [unpopular_total]
  have hh := Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ A)
    ((A+A) \ popularSums A ε) (fun p : ℝ × ℝ => p.1+p.2)
  change _ = ∑ s ∈ (A+A) \ popularSums A ε,
    ((A ×ˢ A).filter (fun p => p.1+p.2=s)).card
  rw [hh]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hsum := Finset.add_mem_add (Finset.mem_product.mp hp).1
    (Finset.mem_product.mp hp).2
  simp only [Finset.mem_sdiff, hsum, true_and]

theorem unpopular_bound (A : Finset ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ a ∈ A, (unpopularCount A ε a : ℝ)) ≤ ε * (A.card : ℝ)^2 := by
  classical
  by_cases hA : A = ∅
  · subst A
    simp
  have hne := Finset.nonempty_iff_ne_empty.mpr hA
  obtain ⟨a, ha⟩ := hne
  have hs : 0 < ((A+A).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a+a, Finset.add_mem_add ha ha⟩
  have he : (∑ a ∈ A, (unpopularCount A ε a : ℝ)) =
      ∑ s ∈ (A+A) \ popularSums A ε, (sumCount A A s : ℝ) := by
    exact_mod_cast unpopular_by_sum A ε
  rw [he]
  calc
    (∑ s ∈ (A+A) \ popularSums A ε, (sumCount A A s : ℝ)) ≤
        ∑ _s ∈ (A+A) \ popularSums A ε, ε*(A.card : ℝ)^2/(A+A).card := by
      apply Finset.sum_le_sum
      intro s hs'
      have hm := Finset.mem_sdiff.mp hs'
      have hn : ¬ ε*(A.card : ℝ)^2/(A+A).card ≤ (sumCount A A s : ℝ) := by
        intro h
        exact hm.2 (Finset.mem_filter.mpr ⟨hm.1,h⟩)
      exact (lt_of_not_ge hn).le
    _ ≤ ∑ _s ∈ A+A, ε*(A.card : ℝ)^2/(A+A).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.sdiff_subset
      · intros; positivity
    _ = ε*(A.card : ℝ)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp [ne_of_gt hs]

theorem popular_rich_retention (A : Finset ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    (A.card : ℝ) ≤ (richRows A (unpopularCount A ε)).card + 2*ε*A.card :=
  richRows_retention A (unpopularCount A ε) ε (unpopular_bound A ε hε)

end Erdos52.RSFresh

-- END RSProof/PopularSums.lean

-- BEGIN RSProof/EnergyRegularization.lean

open scoped BigOperators Pointwise

namespace Erdos52.RSFresh

def regularizationSeq {α : Type*} (R : Finset α → Finset α) (A : Finset α) :
    ℕ → Finset α
  | 0 => A
  | t + 1 => R (regularizationSeq R A t)

theorem regularizationSeq_subset {α : Type*} (R : Finset α → Finset α)
    (A : Finset α) (hR : ∀ X ⊆ A, R X ⊆ X) (t : ℕ) :
    regularizationSeq R A t ⊆ A := by
  induction t with
  | zero => exact Finset.Subset.refl A
  | succ t ih => exact (hR _ ih).trans ih

theorem regularizationSeq_card {α : Type*} (R : Finset α → Finset α)
    (A : Finset α) (q : ℝ) (hR : ∀ X ⊆ A, R X ⊆ X)
    (hcard : ∀ X ⊆ A, (X.card : ℝ) ≤ (R X).card + q) (t : ℕ) :
    (A.card : ℝ) ≤ (regularizationSeq R A t).card + (t : ℝ) * q := by
  induction t with
  | zero => simp [regularizationSeq]
  | succ t ih =>
    have hc := hcard _ (regularizationSeq_subset R A hR t)
    simp only [regularizationSeq, Nat.cast_add, Nat.cast_one]
    linarith

theorem exists_energy_regularization {α : Type*} (R : Finset α → Finset α)
    (A : Finset α) (E : Finset α → ℝ) (L : ℕ) (hL : 0 < L)
    (hA : A.Nonempty) (hpow : 8 * (A.card : ℝ) ≤ (2 : ℝ) ^ L)
    (hR : ∀ X ⊆ A, R X ⊆ X)
    (hcard : ∀ X ⊆ A,
      (X.card : ℝ) ≤ (R X).card + (A.card : ℝ) / (8 * (L : ℝ)))
    (hlower : ∀ X ⊆ A, (X.card : ℝ) ^ 2 ≤ E X)
    (hupper : E A ≤ (A.card : ℝ) ^ 3) :
    ∃ B ⊆ A, (A.card : ℝ) ≤ 2 * (B.card : ℝ) ∧ E B ≤ 2 * E (R B) := by
  have hn : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hq : 0 ≤ (A.card : ℝ) / (8 * (L : ℝ)) := by positivity
  have hmass (t : ℕ) (ht : t ≤ L) :
      (A.card : ℝ) ≤ 2 * ((regularizationSeq R A t).card : ℝ) := by
    have hc := regularizationSeq_card R A
      ((A.card : ℝ) / (8 * (L : ℝ))) hR hcard t
    have ht' : (t : ℝ) ≤ L := by exact_mod_cast ht
    have hmul := mul_le_mul_of_nonneg_right ht' hq
    have he : (L : ℝ) * ((A.card : ℝ) / (8 * (L : ℝ))) =
        (A.card : ℝ) / 8 := by field_simp [ne_of_gt hLr]
    rw [he] at hmul
    linarith
  by_contra hnone
  have hstep (t : ℕ) (ht : t < L) :
      2 * E (regularizationSeq R A (t + 1)) < E (regularizationSeq R A t) := by
    have hs := regularizationSeq_subset R A hR t
    have hm := hmass t ht.le
    have hnot : ¬ E (regularizationSeq R A t) ≤
        2 * E (R (regularizationSeq R A t)) := by
      intro he
      exact hnone ⟨_, hs, hm, he⟩
    exact lt_of_not_ge hnot
  have henergy : ∀ t : ℕ, t ≤ L →
      (2 : ℝ) ^ t * E (regularizationSeq R A t) ≤ E A := by
    intro t
    induction t with
    | zero => intro _; simp [regularizationSeq]
    | succ t ih =>
      intro ht
      have hp := mul_le_mul_of_nonneg_left (hstep t (by omega)).le
        (by positivity : 0 ≤ (2 : ℝ) ^ t)
      have hi := ih (by omega)
      rw [pow_succ]
      nlinarith
  have hm := hmass L le_rfl
  have he := henergy L le_rfl
  have hl := hlower _ (regularizationSeq_subset R A hR L)
  have hc : 0 ≤ ((regularizationSeq R A L).card : ℝ) := by positivity
  have hnonneg : 0 ≤ E (regularizationSeq R A L) := le_trans (sq_nonneg _) hl
  have hp := mul_le_mul_of_nonneg_right hpow hnonneg
  have hsquare : (A.card : ℝ) ^ 2 ≤
      4 * (((regularizationSeq R A L).card : ℝ) ^ 2) := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hsquare hn.le
  have hlowE := mul_le_mul_of_nonneg_left hl
    (by positivity : 0 ≤ 8 * (A.card : ℝ))
  nlinarith [mul_pos hn (sq_pos_of_pos hn)]

end Erdos52.RSFresh

-- END RSProof/EnergyRegularization.lean

-- BEGIN RSProof/RegularizedPopular.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def popularRich (A : Finset ℝ) (ε : ℝ) : Finset ℝ :=
  richRows A (unpopularCount A ε)

theorem popularRich_subset (A : Finset ℝ) (ε : ℝ) : popularRich A ε ⊆ A :=
  richRows_subset A (unpopularCount A ε)

theorem popularRich_neighbors (A : Finset ℝ) (ε a : ℝ) (ha : a ∈ popularRich A ε) :
    A.card ≤ 2 * (A.filter (fun b => a+b ∈ popularSums A ε)).card := by
  classical
  have hb : 2 * unpopularCount A ε a ≤ A.card := (Finset.mem_filter.mp ha).2
  have hp := Finset.card_filter_add_card_filter_not
    (s := A) (p := fun b => a+b ∈ popularSums A ε)
  change (A.filter (fun b => a+b ∈ popularSums A ε)).card + unpopularCount A ε a =
    A.card at hp
  omega

theorem exists_regularized_popular (A : Finset ℝ) (hA : A.Nonempty) :
    ∃ B ⊆ A, (A.card : ℝ) ≤ 2 * (B.card : ℝ) ∧
      (addEnergy B : ℝ) ≤ 2 * (addEnergy
        (popularRich B (1 / (16 * (logBudget A.card : ℝ)))) : ℝ) := by
  let L := logBudget A.card
  have hL : 0 < (L : ℝ) := by exact_mod_cast logBudget_pos A.card
  have hε : 0 ≤ 1 / (16 * (L : ℝ)) := by positivity
  apply exists_energy_regularization
    (fun X => popularRich X (1 / (16 * (L : ℝ)))) A
    (fun X => (addEnergy X : ℝ)) L (logBudget_pos A.card) hA (logBudget_power A.card)
  · intro X hX
    exact popularRich_subset X _
  · intro X hX
    have hc := popular_rich_retention X (1 / (16 * (L : ℝ))) hε
    have hx : (X.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hX
    have he : 2 * (1 / (16 * (L : ℝ))) * (X.card : ℝ) =
        (X.card : ℝ) / (8 * (L : ℝ)) := by
      field_simp
      ring
    rw [he] at hc
    exact hc.trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right hx (by positivity : 0 ≤ 8 * (L : ℝ))))
  · intro X hX
    exact_mod_cast addEnergy_lower X
  · exact_mod_cast addEnergy_upper A

end Erdos52.RSFresh

-- END RSProof/RegularizedPopular.lean

-- BEGIN RSProof/EnergyClass.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem diffCount_mono {A B C D : Finset ℝ} (hA : A ⊆ C) (hB : B ⊆ D) (t : ℝ) :
    diffCount A B t ≤ diffCount C D t := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA (Finset.mem_product.mp hp).1,
    hB (Finset.mem_product.mp hp).2⟩,he⟩

 theorem energyLogBudget_mono {n m : ℕ} (h : n ≤ m) : logBudget n ≤ logBudget m := by
  unfold logBudget
  exact Nat.add_le_add_right (Nat.log_mono_right h) _

 theorem exists_energy_class (B R : Finset ℝ) (L : ℕ) (hB : B.Nonempty) (hR : R ⊆ B)
    (hL : logBudget B.card ≤ L) (hE : (addEnergy B:ℝ) ≤ 2*(addEnergy R:ℝ)) :
    ∃ D ⊆ R-R, D.Nonempty ∧ ∃ delta : ℕ, 0<delta ∧
      (∀ d ∈ D, delta ≤ diffCount R R d) ∧
      (addEnergy B:ℝ) ≤ 8*(L:ℝ)*(D.card:ℝ)*(delta:ℝ)^2 := by
  classical
  obtain ⟨j,hj,he⟩ := exists_dyadic_square_class (R-R) (diffCount R R) R.card
    (fun _ h => diffCount_pos h) (fun d _ => diffCount_le_left R R d)
  let D := dyadicClass (R-R) (diffCount R R) j
  have hh : addEnergy R ≤ 4*logBudget R.card*D.card*(2^j)^2 := he
  have hl : logBudget R.card ≤ L := (energyLogBudget_mono (Finset.card_le_card hR)).trans hL
  have he' : (addEnergy B:ℝ) ≤ 8*(L:ℝ)*(D.card:ℝ)*((2:ℝ)^j)^2 := by
    have hhr : (addEnergy R:ℝ) ≤ 4*(logBudget R.card:ℝ)*(D.card:ℝ)*((2:ℝ)^j)^2 := by exact_mod_cast hh
    have hlr : (logBudget R.card:ℝ)≤L := by exact_mod_cast hl
    have hu := mul_le_mul_of_nonneg_right hlr (by positivity : 0≤4*(D.card:ℝ)*((2:ℝ)^j)^2)
    nlinarith
  have hn : D.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hz,Finset.card_empty,Nat.cast_zero,mul_zero,zero_mul] at he'
    have hlo := addEnergy_lower B
    have hb := Finset.card_pos.mpr hB
    have hEr : (0:ℝ)<addEnergy B := by exact_mod_cast (by nlinarith : 0<addEnergy B)
    linarith
  refine ⟨D,Finset.filter_subset _ _,hn,2^j,by positivity,?_,?_⟩
  · intro d hd
    exact (dyadicClass_bounds (R-R) (diffCount R R) (fun _ h => diffCount_pos h) j hd).1
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using he'

end Erdos52.RSFresh

-- END RSProof/EnergyClass.lean

-- BEGIN RSProof/ImageCauchy.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem image_cauchy {α β : Type*} [DecidableEq β] (S : Finset α) (U : Finset β) (f : α → β)
    (hf : ∀ x ∈ S, f x ∈ U) :
    S.card^2 ≤ U.card*((S ×ˢ S).filter (fun p => f p.1=f p.2)).card := by
  classical
  have hsum := Finset.card_eq_sum_card_fiberwise hf
  rw [← fiber_square_sum S U f hf]
  have h := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1:ℕ)) (fun v => (S.filter (fun x => f x=v)).card)
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,← hsum] using h

end Erdos52.RSFresh

-- END RSProof/ImageCauchy.lean

-- BEGIN RSProof/TripleFiber.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem triple_fiber_count {α β : Type*} [DecidableEq β] (S : Finset α) (U : Finset β) (f : α → β)
    (hf : ∀ x ∈ S, f x ∈ U) :
    ((S ×ˢ (S ×ˢ S)).filter (fun p => f p.1=f p.2.1 ∧ f p.1=f p.2.2)).card =
      ∑ v ∈ U, (S.filter (fun x => f x=v)).card^3 := by
  classical
  let F : β → Finset (α × (α × α)) := fun v =>
    (S.filter (fun x => f x=v)) ×ˢ ((S.filter (fun x => f x=v)) ×ˢ (S.filter (fun x => f x=v)))
  have hd : (U : Set β).PairwiseDisjoint F := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have h1 := (Finset.mem_filter.mp (Finset.mem_product.mp hpa).1).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_product.mp hpb).1).2
    exact hab (h1.symm.trans h2)
  have he : (S ×ˢ (S ×ˢ S)).filter (fun p => f p.1=f p.2.1 ∧ f p.1=f p.2.2) = U.disjiUnion F hd := by
    ext p
    simp only [Finset.mem_disjiUnion,F,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨h1,h2,h3⟩,he2,he3⟩
      exact ⟨f p.1,hf p.1 h1,⟨h1,rfl⟩,⟨h2,he2.symm⟩,h3,he3.symm⟩
    · rintro ⟨v,hv,⟨h1,e1⟩,⟨h2,e2⟩,h3,e3⟩
      exact ⟨⟨h1,h2,h3⟩,e1.trans e2.symm,e1.trans e3.symm⟩
  rw [he,Finset.card_disjiUnion]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [F,Finset.card_product]
  ring

end Erdos52.RSFresh

-- END RSProof/TripleFiber.lean

-- BEGIN RSProof/TripleCollision.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem triple_sum_collision_bound (B : Finset ℝ) (S : Finset (ℝ × (ℝ × ℝ)))
    (hS : S ⊆ B ×ˢ (B ×ˢ B)) :
    ((S ×ˢ S).filter (fun z => (z.1.1+z.1.2.1,z.1.1+z.1.2.2)=
      (z.2.1+z.2.2.1,z.2.1+z.2.2.2))).card ≤ energy3 B B := by
  classical
  let U := B ×ˢ B
  let Q := (U ×ˢ (U ×ˢ U)).filter (fun z => z.1.1-z.1.2=z.2.1.1-z.2.1.2 ∧ z.1.1-z.1.2=z.2.2.1-z.2.2.2)
  have hQ : Q.card=energy3 B B := triple_fiber_count U (B-B) (fun p => p.1-p.2)
    (fun p hp => Finset.sub_mem_sub (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  rw [← hQ]
  let F : (ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ)) → (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun z => ((z.1.1,z.2.1),((z.2.2.1,z.1.2.1),(z.2.2.2,z.1.2.2)))
  apply Finset.card_le_card_of_injOn F
  · intro z hz
    obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
    have h1 := hS (Finset.mem_product.mp hz).1
    have h2 := hS (Finset.mem_product.mp hz).2
    have he1 := congrArg (fun p : ℝ × ℝ => p.1) he
    have he2 := congrArg (fun p : ℝ × ℝ => p.2) he
    simp only [Finset.mem_product] at h1 h2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h1.1,h2.1⟩,
        Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h2.2.1,h1.2.1⟩,
        Finset.mem_product.mpr ⟨h2.2.2,h1.2.2⟩⟩⟩
    · dsimp [F]
      dsimp at he1 he2
      constructor <;> linarith
  · intro z hz w hw he
    rcases z with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
    rcases w with ⟨⟨a',b',c'⟩,⟨d',e',f'⟩⟩
    simp only [F,Prod.mk.injEq] at he ⊢
    tauto

end Erdos52.RSFresh

-- END RSProof/TripleCollision.lean

-- BEGIN RSProof/PopularTriples.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem popular_triple_lower (B R D P : Finset ℝ) (delta : ℕ)
    (hR : R ⊆ B) (hpop : ∀ b ∈ R, B.card ≤ 2*(B.filter (fun a => a+b∈P)).card)
    (hD : ∀ d ∈ D, delta ≤ diffCount R R d) :
    (B.card*D.card*delta)^2 ≤ 4*(differencePairs P (B+B) D).card*energy3 B B := by
  classical
  let C := differencePairs R R D
  let S := (B ×ˢ C).filter (fun z => z.1+z.2.1∈P)
  have hC : D.card*delta ≤ C.card := by
    rw [differencePairs_card]
    calc
      _ = ∑ _d ∈ D, delta := by simp
      _ ≤ _ := Finset.sum_le_sum hD
  have hS : S.card = ∑ z ∈ C, (B.filter (fun a => a+z.1∈P)).card := by
    simp only [S,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
    exact Finset.sum_comm
  have hlow : B.card*D.card*delta ≤ 2*S.card := by
    have hh : B.card*C.card ≤ 2*S.card := by
      rw [hS,Finset.mul_sum]
      calc
        _ = ∑ _z ∈ C, B.card := by simp [Nat.mul_comm]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro z hz
          exact hpop z.1 (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
    have hh' := Nat.mul_le_mul_left B.card hC
    nlinarith
  have hsub : S ⊆ B ×ˢ (B ×ˢ B) := by
    intro z hz
    obtain ⟨hz,hp⟩ := Finset.mem_filter.mp hz
    have hbc := (Finset.mem_filter.mp (Finset.mem_product.mp hz).2).1
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hz).1,
      Finset.mem_product.mpr ⟨hR (Finset.mem_product.mp hbc).1,hR (Finset.mem_product.mp hbc).2⟩⟩
  have himg : ∀ z ∈ S, (z.1+z.2.1,z.1+z.2.2) ∈ differencePairs P (B+B) D := by
    intro z hz
    obtain ⟨hz,hp⟩ := Finset.mem_filter.mp hz
    have hbc := Finset.mem_filter.mp (Finset.mem_product.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hp,Finset.add_mem_add (Finset.mem_product.mp hz).1
      (hR (Finset.mem_product.mp hbc.1).2)⟩,?_⟩
    simpa only [add_sub_add_left_eq_sub] using hbc.2
  have hcs := image_cauchy S (differencePairs P (B+B) D) (fun z => (z.1+z.2.1,z.1+z.2.2)) himg
  have hcol := triple_sum_collision_bound B S hsub
  have hm := Nat.mul_le_mul_left (differencePairs P (B+B) D).card hcol
  have hp := Nat.pow_le_pow_left hlow 2
  nlinarith

end Erdos52.RSFresh

-- END RSProof/PopularTriples.lean

-- BEGIN RSProof/FirstCoordinateLift.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem first_coordinate_fiber {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (T : Finset γ) (f : α → β) (q : β × γ) (hq : q.2∈T) :
    ((S ×ˢ T).filter (fun z => (f z.1,z.2)=q)).card = (S.filter (fun x => f x=q.1)).card := by
  classical
  rw [card_filter_product S T (fun x y => (f x,y)=q)]
  calc
    _ = ∑ x ∈ S, if f x=q.1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases he : f x=q.1
      · have hh : (T.filter (fun y => (f x,y)=q)) = {q.2} := by
          ext y
          simp only [Finset.mem_filter,Finset.mem_singleton]
          constructor
          · rintro ⟨hy,heq⟩
            exact congrArg (fun z : β × γ => z.2) heq
          · intro hy
            subst y
            exact ⟨hq,Prod.ext he rfl⟩
        simp only [hh,if_pos he,Finset.card_singleton]
      · have hh : (T.filter (fun y => (f x,y)=q)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact he (congrArg (fun z : β × γ => z.1) (Finset.mem_filter.mp hy).2)
        simp [hh,he]
    _ = _ := by simp only [Finset.sum_boole,Nat.cast_id]

 theorem first_coordinate_lift {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (T : Finset γ) (Q : Finset (β × γ)) (f : α → β)
    (hQ : ∀ q ∈ Q, q.2∈T) :
    (∑ q ∈ Q, (S.filter (fun x => f x=q.1)).card) =
      ((S ×ˢ T).filter (fun z => (f z.1,z.2)∈Q)).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter (S ×ˢ T) Q (fun z => (f z.1,z.2))
  rw [← h]
  apply Finset.sum_congr rfl
  intro q hq
  exact (first_coordinate_fiber S T f q (hQ q hq)).symm

end Erdos52.RSFresh

-- END RSProof/FirstCoordinateLift.lean

-- BEGIN RSProof/PopularLift.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

noncomputable def sumDifferenceTriples (B S D : Finset ℝ) :=
  ((B ×ˢ B) ×ˢ S).filter (fun z => z.1.1+z.1.2-z.2∈D)

 theorem popular_lift (B S D : Finset ℝ) (eps : ℝ) (_heps : 0≤eps) :
    eps*(B.card:ℝ)^2*(differencePairs (popularSums B eps) S D).card ≤
      ((B+B).card:ℝ)*(sumDifferenceTriples B S D).card := by
  classical
  let P := popularSums B eps
  let Q := differencePairs P S D
  by_cases he : B=∅
  · subst B
    simp
  have hB := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨b,hb⟩ := hB
  have hs : (0:ℝ)<(B+B).card := by exact_mod_cast Finset.card_pos.mpr ⟨b+b,Finset.add_mem_add hb hb⟩
  have hl : (eps*(B.card:ℝ)^2/(B+B).card)*(Q.card:ℝ) ≤ ∑ q ∈ Q, (sumCount B B q.1:ℝ) := by
    calc
      _ = ∑ _q ∈ Q, eps*(B.card:ℝ)^2/(B+B).card := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        have hmem := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
        exact (Finset.mem_filter.mp hmem).2
  have hcard : (∑ q ∈ Q, sumCount B B q.1) ≤ (sumDifferenceTriples B S D).card := by
    rw [show (∑ q ∈ Q, sumCount B B q.1) =
      (((B ×ˢ B) ×ˢ S).filter (fun z => (z.1.1+z.1.2,z.2)∈Q)).card from
        first_coordinate_lift (B ×ˢ B) S Q (fun z => z.1+z.2)
          (fun q hq => (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hz,hq⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz,(Finset.mem_filter.mp hq).2⟩
  have hcr : (∑ q ∈ Q, (sumCount B B q.1:ℝ)) ≤ (sumDifferenceTriples B S D).card := by exact_mod_cast hcard
  have hh := mul_le_mul_of_nonneg_left (hl.trans hcr) hs.le
  have heq : (B+B).card*((eps*(B.card:ℝ)^2/(B+B).card)*(Q.card:ℝ)) = eps*(B.card:ℝ)^2*Q.card := by field_simp
  rw [heq] at hh
  exact hh

end Erdos52.RSFresh

-- END RSProof/PopularLift.lean

-- BEGIN RSProof/CountSymmetry.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem diffCount_swap_neg (A B : Finset ℝ) (t : ℝ) : diffCount B A (-t)=diffCount A B t := by
  classical
  apply Finset.card_equiv (Equiv.prodComm ℝ ℝ)
  intro p
  simp only [Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
  constructor
  · rintro ⟨⟨hb,ha⟩,he⟩
    exact ⟨⟨ha,hb⟩,by dsimp at he ⊢; linarith⟩
  · rintro ⟨⟨ha,hb⟩,he⟩
    exact ⟨⟨hb,ha⟩,by dsimp at he ⊢; linarith⟩

 theorem energy3_symm (A B : Finset ℝ) : energy3 A B=energy3 B A := by
  classical
  apply Finset.sum_bij (fun t _ => -t)
  · intro t ht
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp ht
    exact Finset.mem_sub.mpr ⟨b,hb,a,ha,by ring⟩
  · intro t ht u hu he
    exact neg_injective he
  · intro t ht
    obtain ⟨b,hb,a,ha,rfl⟩ := Finset.mem_sub.mp ht
    exact ⟨a-b,Finset.sub_mem_sub ha hb,by ring⟩
  · intro t ht
    rw [diffCount_swap_neg]

end Erdos52.RSFresh

-- END RSProof/CountSymmetry.lean

-- BEGIN RSProof/CountSupport.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem diffCount_zero {A B : Finset ℝ} {t : ℝ} (ht : t ∉ A-B) : diffCount A B t=0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  exact ht (he ▸ Finset.sub_mem_sub (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)

 theorem diffCount_sum_superset (A B U : Finset ℝ) (hU : A-B ⊆ U) :
    ∑ t ∈ U, diffCount A B t = A.card*B.card := by
  classical
  rw [← sum_diffCount A B]
  symm
  exact Finset.sum_subset hU (fun t ht hn => diffCount_zero hn)

 theorem energy3_sum_superset (A B U : Finset ℝ) (hU : A-B ⊆ U) :
    ∑ t ∈ U, (diffCount A B t)^3 = energy3 A B := by
  classical
  symm
  exact Finset.sum_subset hU (fun t ht hn => by rw [diffCount_zero hn]; norm_num)

end Erdos52.RSFresh

-- END RSProof/CountSupport.lean

-- BEGIN RSProof/MomentInterpolation.lean

open scoped BigOperators
namespace Erdos52.RSFresh

 theorem half_moment_four {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    (∑ x ∈ S, f x*Real.sqrt (f x))^4 ≤ (∑ x ∈ S, f x)^3*(∑ x ∈ S, (f x)^3) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => Real.sqrt (f x)) f
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => Real.sqrt (f x)) (fun x => f x*Real.sqrt (f x))
  have hs : (∑ x ∈ S, (Real.sqrt (f x))^2) = ∑ x ∈ S, f x :=
    Finset.sum_congr rfl (fun x hx => Real.sq_sqrt (hf x hx))
  have hm : (∑ x ∈ S, Real.sqrt (f x)*(f x*Real.sqrt (f x))) = ∑ x ∈ S, (f x)^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    nlinarith [Real.sq_sqrt (hf x hx)]
  have ht : (∑ x ∈ S, (f x*Real.sqrt (f x))^2) = ∑ x ∈ S, (f x)^3 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_pow,Real.sq_sqrt (hf x hx)]
    ring
  rw [hs] at h1
  simp only [mul_comm (Real.sqrt _) (f _)] at h1
  rw [hs,hm,ht] at h2
  have h0 : 0 ≤ ∑ x ∈ S, f x := Finset.sum_nonneg hf
  have hE : 0 ≤ ∑ x ∈ S, (f x)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h3 := pow_le_pow_left₀ (sq_nonneg (∑ x ∈ S, f x*Real.sqrt (f x))) h1 2
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (∑ x ∈ S, f x))
  nlinarith

 theorem holder_cube {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) (hg : ∀ x ∈ S, 0 ≤ g x) :
    (∑ x ∈ S, f x*g x)^3 ≤ (∑ x ∈ S, f x*Real.sqrt (f x))^2*(∑ x ∈ S, (g x)^3) := by
  let R := ∑ x ∈ S, f x*g x
  let F := ∑ x ∈ S, f x*Real.sqrt (f x)
  let H := ∑ x ∈ S, Real.sqrt (f x)*(g x)^2
  let G := ∑ x ∈ S, (g x)^3
  have hr : 0 ≤ R := Finset.sum_nonneg (fun x hx => mul_nonneg (hf x hx) (hg x hx))
  have hh : 0 ≤ H := Finset.sum_nonneg (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
  have h1 : R^2 ≤ F*H := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      S (fun x hx => mul_nonneg (hf x hx) (Real.sqrt_nonneg _))
      (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
    intro x hx
    have he := Real.sq_sqrt (hf x hx)
    calc
      (f x*g x)^2 = f x*(Real.sqrt (f x))^2*(g x)^2 := by rw [he]; ring
      _ ≤ _ := by ring_nf; exact le_rfl
  have h2 : H^2 ≤ R*G := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      S (fun x hx => mul_nonneg (hf x hx) (hg x hx))
      (fun x hx => pow_nonneg (hg x hx) 3)
    intro x hx
    rw [mul_pow,Real.sq_sqrt (hf x hx)]
    nlinarith
  have h3 := pow_le_pow_left₀ (sq_nonneg R) h1 2
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg F)
  change R^3 ≤ F^2*G
  by_cases hz : R=0
  · simp [hz]
    exact mul_nonneg (sq_nonneg F) (Finset.sum_nonneg (fun x hx => pow_nonneg (hg x hx) 3))
  · have hp : 0<R := lt_of_le_of_ne hr (Ne.symm hz)
    apply le_of_mul_le_mul_right (a := R) _ hp
    nlinarith

 theorem inner_six_moment {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) (hg : ∀ x ∈ S, 0 ≤ g x) :
    (∑ x ∈ S, f x*g x)^6 ≤
      (∑ x ∈ S, f x)^3*(∑ x ∈ S, (f x)^3)*(∑ x ∈ S, (g x)^3)^2 := by
  have h1 := holder_cube S f g hf hg
  have h2 := half_moment_four S f hf
  have hr : 0 ≤ ∑ x ∈ S, f x*g x := Finset.sum_nonneg (fun x hx => mul_nonneg (hf x hx) (hg x hx))
  have h3 := pow_le_pow_left₀ (pow_nonneg hr 3) h1 2
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (∑ x ∈ S, (g x)^3))
  nlinarith

end Erdos52.RSFresh

-- END RSProof/MomentInterpolation.lean

-- BEGIN RSProof/SumDifferenceMoment.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem sumDifferenceTriples_fibers (B S D : Finset ℝ) :
    (sumDifferenceTriples B S D).card =
      (((B ×ˢ D) ×ˢ (S ×ˢ B)).filter (fun z => z.1.1-z.1.2=z.2.1-z.2.2)).card := by
  classical
  apply Finset.card_bij (fun z _ => ((z.1.1,z.1.1+z.1.2-z.2),(z.2,z.1.2)))
  · intro z hz
    obtain ⟨hz,hd⟩ := Finset.mem_filter.mp hz
    have hbb := Finset.mem_product.mp (Finset.mem_product.mp hz).1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hbb.1,hd⟩,
      Finset.mem_product.mpr ⟨(Finset.mem_product.mp hz).2,hbb.2⟩⟩,by dsimp; ring⟩
  · intro z hz w hw he
    have h1 := congrArg (fun p : (ℝ×ℝ)×(ℝ×ℝ) => p.1.1) he
    have h2 := congrArg (fun p : (ℝ×ℝ)×(ℝ×ℝ) => p.2.2) he
    have h3 := congrArg (fun p : (ℝ×ℝ)×(ℝ×ℝ) => p.2.1) he
    exact Prod.ext (Prod.ext h1 h2) h3
  · intro z hz
    obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
    have hbd := Finset.mem_product.mp (Finset.mem_product.mp hz).1
    have hsb := Finset.mem_product.mp (Finset.mem_product.mp hz).2
    refine ⟨((z.1.1,z.2.2),z.2.1),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hbd.1,hsb.2⟩,hsb.1⟩,?_⟩
      have heq : z.1.1+z.2.2-z.2.1=z.1.2 := by linarith
      exact heq.symm ▸ hbd.2
    · apply Prod.ext
      · change (z.1.1,z.1.1+z.2.2-z.2.1)=z.1
        apply Prod.ext
        · rfl
        · dsimp only
          linarith
      · rfl

 theorem sumDifferenceTriples_six (B S D : Finset ℝ) :
    (sumDifferenceTriples B S D).card^6 ≤
      (B.card*D.card)^3*energy3 B D*(energy3 B S)^2 := by
  classical
  let U := (B-D) ∪ (S-B)
  have hB : B-D ⊆ U := Finset.subset_union_left
  have hS : S-B ⊆ U := Finset.subset_union_right
  have hr : (sumDifferenceTriples B S D).card = ∑ t ∈ U, diffCount B D t*diffCount S B t := by
    rw [sumDifferenceTriples_fibers]
    exact mixed_fiber_collision (B ×ˢ D) (S ×ˢ B) U (fun p => p.1-p.2) (fun p => p.1-p.2)
      (fun p hp => hB (Finset.sub_mem_sub (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2))
  have h := inner_six_moment U (fun t => (diffCount B D t:ℝ)) (fun t => (diffCount S B t:ℝ))
    (fun _ _ => by positivity) (fun _ _ => by positivity)
  have hn : (∑ t ∈ U, diffCount B D t*diffCount S B t)^6 ≤
      (∑ t ∈ U, diffCount B D t)^3*(∑ t ∈ U, (diffCount B D t)^3)*
        (∑ t ∈ U, (diffCount S B t)^3)^2 := by exact_mod_cast h
  rw [← hr,diffCount_sum_superset B D U hB,energy3_sum_superset B D U hB,
    energy3_sum_superset S B U hS,energy3_symm S B] at hn
  exact hn

end Erdos52.RSFresh

-- END RSProof/SumDifferenceMoment.lean

-- BEGIN RSProof/AddEnergyBridge.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 def swapSeconds : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ ((ℝ × ℝ) × (ℝ × ℝ)) where
  toFun p := ((p.1.1,p.2.2),(p.2.1,p.1.2))
  invFun p := ((p.1.1,p.2.2),(p.2.1,p.1.2))
  left_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl

 theorem addEnergy_eq_native (A : Finset ℝ) : addEnergy A = Finset.addEnergy A A := by
  classical
  rw [addEnergy, energy2_eq_collision, Finset.addEnergy_eq_card_filter]
  apply Finset.card_equiv swapSeconds
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  change ((a∈A ∧ b∈A) ∧ c∈A ∧ d∈A) ∧ a-b=c-d ↔
    ((a∈A ∧ d∈A) ∧ c∈A ∧ b∈A) ∧ a+d=c+b
  constructor
  · rintro ⟨⟨⟨ha,hb⟩,hc,hd⟩,he⟩
    exact ⟨⟨⟨ha,hd⟩,hc,hb⟩,by linarith⟩
  · rintro ⟨⟨⟨ha,hd⟩,hc,hb⟩,he⟩
    exact ⟨⟨⟨ha,hb⟩,hc,hd⟩,by linarith⟩

 theorem addEnergy_eq_sum_sumCount_sq (A : Finset ℝ) :
    addEnergy A = ∑ t ∈ A+A, (sumCount A A t)^2 := by
  classical
  rw [addEnergy_eq_native, Finset.addEnergy_eq_sum_sq']
  rfl

 theorem addEnergy_mono {A B : Finset ℝ} (h : A ⊆ B) : addEnergy A ≤ addEnergy B := by
  rw [addEnergy_eq_native, addEnergy_eq_native]
  exact Finset.addEnergy_mono h h

 theorem card_four_le_sum_card_mul_energy (A : Finset ℝ) :
    A.card^4 ≤ (A+A).card*addEnergy A := by
  classical
  rw [addEnergy_eq_native]
  have h := Finset.le_card_add_mul_addEnergy A A
  nlinarith

end Erdos52.RSFresh

-- END RSProof/AddEnergyBridge.lean

-- BEGIN RSProof/RegularizedFewProducts.lean

open scoped BigOperators Pointwise
namespace Erdos52.RSFresh

 theorem regularized_few_products (B P : Finset ℝ) (T L : ℕ) (hB : B.Nonempty)
    (hP : ∀ p ∈ P, p≠0) (hBP : B.card≤P.card)
    (hT : ∀ b ∈ B, T ≤ ratioCount P P b) (hL : logBudget B.card ≤ L)
    (hreg : (addEnergy B:ℝ) ≤ 2*(addEnergy (popularRich B (1/(16*(L:ℝ)))):ℝ)) :
    (B.card:ℝ)^41*(T:ℝ)^33 ≤ fewProductsConstant*(P.card:ℝ)^44*((B+B).card:ℝ)^19*(L:ℝ)^24 := by
  classical
  let eps : ℝ := 1/(16*(L:ℝ))
  let R := popularRich B eps
  have hRB : R ⊆ B := popularRich_subset B eps
  have hL0 : 0<L := (logBudget_pos B.card).trans_le hL
  have hLr : (0:ℝ)<L := by exact_mod_cast hL0
  have hBr : (0:ℝ)<B.card := by exact_mod_cast Finset.card_pos.mpr hB
  obtain ⟨D,hDR,hD,delta,hd0,hdelta,hloc⟩ := exists_energy_class B R L hB hRB hL hreg
  have hDB : D ⊆ B-B := hDR.trans (Finset.sub_subset_sub hRB hRB)
  have hdr : (0:ℝ)<D.card := by exact_mod_cast Finset.card_pos.mpr hD
  let S := B+B
  let Q := differencePairs (popularSums B eps) S D
  let Z := sumDifferenceTriples B S D
  have htrip := popular_triple_lower B R D (popularSums B eps) delta hRB
    (fun b hb => by simpa only [add_comm] using popularRich_neighbors B eps b hb) hdelta
  have htripr : (B.card:ℝ)^2*(D.card:ℝ)^2*(delta:ℝ)^2 ≤ 4*(Q.card:ℝ)*(energy3 B B:ℝ) := by
    have hh : ((B.card*D.card*delta:ℕ):ℝ)^2 ≤ 4*(Q.card:ℝ)*(energy3 B B:ℝ) := by exact_mod_cast htrip
    push_cast at hh
    nlinarith
  have hpop := popular_lift B S D eps (by dsimp [eps]; positivity)
  have hpopr : (B.card:ℝ)^2*(Q.card:ℝ) ≤ 16*(L:ℝ)*(S.card:ℝ)*(Z.card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpop (by positivity : 0≤16*(L:ℝ))
    have he : (16*(L:ℝ))*(eps*(B.card:ℝ)^2*(Q.card:ℝ)) = (B.card:ℝ)^2*(Q.card:ℝ) := by
      dsimp [eps]
      field_simp
    change (16*(L:ℝ))*(eps*(B.card:ℝ)^2*(Q.card:ℝ)) ≤ _ at hh
    rw [he] at hh
    change (B.card:ℝ)^2*(Q.card:ℝ) ≤ _
    nlinarith
  have hmain : (B.card:ℝ)^4*(D.card:ℝ)^2*(delta:ℝ)^2 ≤
      64*(L:ℝ)*(energy3 B B:ℝ)*(S.card:ℝ)*(Z.card:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left htripr (sq_nonneg (B.card:ℝ))
    have h2 := mul_le_mul_of_nonneg_right hpopr (by positivity : 0≤4*(energy3 B B:ℝ))
    nlinarith
  have hC (X : Finset ℝ) : (energy3 B X:ℝ)*(T:ℝ)^3 ≤
      cubicConstant*(P.card:ℝ)^4*(X.card:ℝ)^2*(L:ℝ) := by
    have hh := ratio_cubic_energy B X P T hP hBP hT
    have hlr : (logBudget B.card:ℝ) ≤ L := by exact_mod_cast hL
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by positivity))
  have hZ : (Z.card:ℝ)^6 ≤ ((B.card:ℝ)*(D.card:ℝ))^3*(energy3 B D:ℝ)*(energy3 B S:ℝ)^2 := by
    exact_mod_cast sumDifferenceTriples_six B S D
  have hcore := few_products_core_power (B.card:ℝ) D.card delta T P.card S.card L
    (energy3 B B) (energy3 B D) (energy3 B S) Z.card hBr hdr
    (by positivity) (by positivity) (by positivity) (by positivity) hLr.le
    (by positivity) (by positivity) (by positivity) (by positivity) hmain hZ (hC B) (hC D) (hC S)
  have hrich := ratio_rich_differences B B D P delta T hP hBP hT hDB
    (fun d hd => (hdelta d hd).trans (diffCount_mono hRB hRB d))
  push_cast at hrich
  have hdE : (addEnergy B:ℝ)*(delta:ℝ)*(T:ℝ)^3 ≤
      cubicConstant*(P.card:ℝ)^4*(B.card:ℝ)^2*(L:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hloc (by positivity : 0≤(delta:ℝ)*(T:ℝ)^3)
    have h2 := mul_le_mul_of_nonneg_left hrich (by positivity : 0≤8*(L:ℝ))
    unfold cubicConstant
    nlinarith
  have henergy : (B.card:ℝ)^4 ≤ (S.card:ℝ)*(addEnergy B:ℝ) := by
    exact_mod_cast card_four_le_sum_card_mul_energy B
  exact few_products_eliminate (B.card:ℝ) D.card delta T P.card S.card L (addEnergy B)
    hBr hdr (by positivity) (by positivity) (by positivity) (by positivity) hLr.le (by positivity)
    hcore hdE hloc henergy

end Erdos52.RSFresh

-- END RSProof/RegularizedFewProducts.lean

-- BEGIN RSProof/FewProducts.lean

open scoped Pointwise
namespace Erdos52.RSFresh

def fewProductsFullConstant : ℝ := 2^41*fewProductsConstant

theorem fewProductsFullConstant_pos : 0<fewProductsFullConstant := by
  norm_num [fewProductsFullConstant,fewProductsConstant,cubicConstant]

 theorem few_products (A P : Finset ℝ) (T : ℕ) (hA : A.Nonempty)
    (hP : ∀ p ∈ P, p≠0) (hAP : A.card≤P.card)
    (hT : ∀ a ∈ A, T ≤ ratioCount P P a) :
    (A.card:ℝ)^41*(T:ℝ)^33 ≤
      fewProductsFullConstant*(P.card:ℝ)^44*((A+A).card:ℝ)^19*(logBudget A.card:ℝ)^24 := by
  classical
  obtain ⟨B,hBA,hcard,hreg⟩ := exists_regularized_popular A hA
  have hB : B.Nonempty := by
    apply Finset.card_pos.mp
    have ha := Finset.card_pos.mpr hA
    have hb : (0:ℝ)<B.card := by
      have har : (0:ℝ)<A.card := by exact_mod_cast ha
      linarith
    exact_mod_cast hb
  have h := regularized_few_products B P T (logBudget A.card) hB hP
    ((Finset.card_le_card hBA).trans hAP) (fun b hb => hT b (hBA hb))
    (energyLogBudget_mono (Finset.card_le_card hBA)) hreg
  have hs : ((B+B).card:ℝ) ≤ (A+A).card := by
    exact_mod_cast Finset.card_le_card (Finset.add_subset_add hBA hBA)
  calc
    _ ≤ (2*(B.card:ℝ))^41*(T:ℝ)^33 := by gcongr
    _ = 2^41*((B.card:ℝ)^41*(T:ℝ)^33) := by ring
    _ ≤ 2^41*(fewProductsConstant*(P.card:ℝ)^44*((B+B).card:ℝ)^19*(logBudget A.card:ℝ)^24) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2^41*(fewProductsConstant*(P.card:ℝ)^44*((A+A).card:ℝ)^19*(logBudget A.card:ℝ)^24) := by
      have hC : 0≤fewProductsConstant := by norm_num [fewProductsConstant,cubicConstant]
      gcongr
    _ = _ := by unfold fewProductsFullConstant; ring

end Erdos52.RSFresh

-- END RSProof/FewProducts.lean

-- BEGIN RSProof/StructureElimination.lean

namespace Erdos52.RSFresh

theorem structure_first_elimination (n u v L s τ b t z Q F : ℝ)
    (hn : 0 < n) (hu : 0 ≤ u) (hv : 0 ≤ v) (hL : 0 ≤ L) (hs : 0 < s)
    (hτ : 0 < τ) (hb : 0 ≤ b) (ht : 0 ≤ t) (hz : 0 ≤ z) (hQ : 0 ≤ Q) (_hF : 0 ≤ F)
    (henergy : n^4 ≤ 4*L*v*s*τ^2)
    (hblock : b*(s*τ^2) ≤ 36*u^2)
    (hslice : s*τ ≤ 2*n*z)
    (hproduct : n^4 ≤ Q*t^2*s*b^8*L^6)
    (hfew : z^41*t^33 ≤ F*u^19*v^44*L^24) :
    n^1106*(s*τ^2)^41*s^8 ≤
      (Q^33*2^82*F^2*36^264*4^264)*u^566*v^352*L^510 := by
  have hp := pow_le_pow_left₀ (pow_nonneg hn.le 4) hproduct 33
  have hsl := pow_le_pow_left₀ (mul_nonneg hs.le hτ.le) hslice 82
  have hf := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hz 41) (pow_nonneg ht 33)) hfew 2
  have hbase : n^50*s^49*τ^82 ≤ (Q^33*2^82*F^2)*b^264*u^38*v^88*L^246 := by
    apply le_of_mul_le_mul_left (a := n^82*s^33) _ (mul_pos (pow_pos hn _) (pow_pos hs _))
    calc
      _ = (n^4)^33*(s*τ)^82 := by ring
      _ ≤ (Q*t^2*s*b^8*L^6)^33*(2*n*z)^82 :=
        mul_le_mul hp hsl (pow_nonneg (mul_nonneg hs.le hτ.le) _) (by positivity)
      _ = (Q^33*2^82*n^82*s^33*b^264*L^198)*(z^41*t^33)^2 := by ring
      _ ≤ (Q^33*2^82*n^82*s^33*b^264*L^198)*(F*u^19*v^44*L^24)^2 := by
        apply mul_le_mul_of_nonneg_left hf
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (pow_nonneg hQ _) (by norm_num)) (pow_nonneg hn.le _))
          (pow_nonneg hs.le _)) (pow_nonneg hb _)) (pow_nonneg hL _)
      _ = _ := by ring
  have hbpow := pow_le_pow_left₀ (by positivity : 0 ≤ b*(s*τ^2)) hblock 264
  have hmiddle : n^50*s^8*(s*τ^2)^305 ≤
      (Q^33*2^82*F^2*36^264)*u^566*v^88*L^246 := by
    calc
      _ = (n^50*s^49*τ^82)*(s*τ^2)^264 := by ring
      _ ≤ ((Q^33*2^82*F^2)*b^264*u^38*v^88*L^246)*(s*τ^2)^264 :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg (mul_nonneg hs.le (sq_nonneg τ)) _)
      _ = (Q^33*2^82*F^2*u^38*v^88*L^246)*(b*(s*τ^2))^264 := by ring
      _ ≤ (Q^33*2^82*F^2*u^38*v^88*L^246)*(36*u^2)^264 := by
        apply mul_le_mul_of_nonneg_left hbpow
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (pow_nonneg hQ _) (by norm_num)) (sq_nonneg F))
          (pow_nonneg hu _)) (pow_nonneg hv _)) (pow_nonneg hL _)
      _ = _ := by
        rw [mul_pow, ← pow_mul]
        have heu : u^566 = u^38*u^528 := by rw [← pow_add]
        rw [heu]
        ac_rfl
  have hep := pow_le_pow_left₀ (pow_nonneg hn.le 4) henergy 264
  calc
    _ = (n^50*s^8*(s*τ^2)^41)*(n^4)^264 := by ring
    _ ≤ (n^50*s^8*(s*τ^2)^41)*(4*L*v*s*τ^2)^264 := by
      apply mul_le_mul_of_nonneg_left hep
      exact mul_nonneg (mul_nonneg (pow_nonneg hn.le _) (pow_nonneg hs.le _))
        (pow_nonneg (mul_nonneg hs.le (sq_nonneg τ)) _)
    _ = (n^50*s^8*(s*τ^2)^305)*(4*L*v)^264 := by
      generalize (4 : ℝ) = a
      ring
    _ ≤ ((Q^33*2^82*F^2*36^264)*u^566*v^88*L^246)*(4*L*v)^264 :=
      mul_le_mul_of_nonneg_right hmiddle (pow_nonneg (by positivity) _)
    _ = _ := by
      generalize (4 : ℝ) = a
      generalize (36 : ℝ) = c
      ring

theorem structure_second_elimination (n u v L s τ b t Q : ℝ)
    (hn : 0 < n) (_hu : 0 ≤ u) (hv : 0 ≤ v) (hL : 0 ≤ L) (hs : 0 < s)
    (hτ : 0 < τ) (hb : 0 ≤ b) (ht : 0 ≤ t) (hQ : 0 ≤ Q)
    (htv : t ≤ v)
    (henergy : n^4 ≤ 4*L*v*s*τ^2)
    (hblock : b*(s*τ^2) ≤ 36*u^2)
    (hproduct : n^4 ≤ Q*t^2*s*b^8*L^6) :
    n^36 ≤ (Q*36^8*4^8)*u^16*v^10*s*L^14 := by
  have htv2 := pow_le_pow_left₀ ht htv 2
  have hp : n^4 ≤ Q*v^2*s*b^8*L^6 := by
    apply hproduct.trans
    gcongr
  have hbpow := pow_le_pow_left₀ (by positivity : 0 ≤ b*(s*τ^2)) hblock 8
  have hmiddle : n^4*(s*τ^2)^8 ≤ Q*36^8*u^16*v^2*s*L^6 := by
    calc
      _ ≤ (Q*v^2*s*b^8*L^6)*(s*τ^2)^8 :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg (mul_nonneg hs.le (sq_nonneg τ)) _)
      _ = (Q*v^2*s*L^6)*(b*(s*τ^2))^8 := by ring
      _ ≤ (Q*v^2*s*L^6)*(36*u^2)^8 := mul_le_mul_of_nonneg_left hbpow (by positivity)
      _ = _ := by ring
  have he := pow_le_pow_left₀ (pow_nonneg hn.le 4) henergy 8
  calc
    n^36 = n^4*(n^4)^8 := by ring
    _ ≤ n^4*(4*L*v*s*τ^2)^8 := mul_le_mul_of_nonneg_left he (pow_nonneg hn.le _)
    _ = (n^4*(s*τ^2)^8)*(4*L*v)^8 := by ring
    _ ≤ (Q*36^8*u^16*v^2*s*L^6)*(4*L*v)^8 :=
      mul_le_mul_of_nonneg_right hmiddle (pow_nonneg (by positivity) _)
    _ = _ := by ring

end Erdos52.RSFresh

-- END RSProof/StructureElimination.lean

-- BEGIN RSProof/RawFinalPower.lean

namespace Erdos52.RSFresh

theorem raw_final_power (n u v L s w C₁ C₂ : ℝ)
    (hn : 0 < n) (hu : 0 ≤ u) (hv : 0 ≤ v) (hL : 0 ≤ L)
    (hs : 0 < s) (hw : 0 < w) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : n^1106*w^41*s^8 ≤ C₁*u^566*v^352*L^510)
    (h₂ : n^36 ≤ C₂*u^16*v^10*s*L^14)
    (h₃ : n^4 ≤ 4*w*v*L) :
    n^1558 ≤ (C₁*C₂^8*4^41)*u^694*v^473*L^663 := by
  have hp₂ := pow_le_pow_left₀ (pow_nonneg hn.le _) h₂ 8
  have hp₃ := pow_le_pow_left₀ (pow_nonneg hn.le _) h₃ 41
  apply le_of_mul_le_mul_left (a := w^41*s^8) _ (mul_pos (pow_pos hw _) (pow_pos hs _))
  calc
    _ = (n^1106*w^41*s^8)*(n^36)^8*(n^4)^41 := by ring
    _ ≤ (C₁*u^566*v^352*L^510)*(C₂*u^16*v^10*s*L^14)^8*(4*w*v*L)^41 := by
      apply mul_le_mul
      · apply mul_le_mul h₁ hp₂
        · exact pow_nonneg (pow_nonneg hn.le _) _
        · exact mul_nonneg (mul_nonneg (mul_nonneg hC₁ (pow_nonneg hu _))
            (pow_nonneg hv _)) (pow_nonneg hL _)
      · exact hp₃
      · exact pow_nonneg (pow_nonneg hn.le _) _
      · exact mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg hC₁ (pow_nonneg hu _)) (pow_nonneg hv _)) (pow_nonneg hL _))
          (pow_nonneg (by positivity) _)
    _ = _ := by ring

end Erdos52.RSFresh

-- END RSProof/RawFinalPower.lean

-- BEGIN RSProof/GlobalPolynomial.lean

open scoped Pointwise
namespace Erdos52.RSFresh

def productBoundConstant : ℝ := 1024*1048704
noncomputable def firstEliminationConstant : ℝ :=
  productBoundConstant^33*2^82*fewProductsFullConstant^2*36^264*4^264
noncomputable def secondEliminationConstant : ℝ := productBoundConstant*36^8*4^8
noncomputable def sumProductConstant : ℝ :=
  firstEliminationConstant*secondEliminationConstant^8*4^41

theorem productBoundConstant_pos : 0 < productBoundConstant := by norm_num [productBoundConstant]
theorem firstEliminationConstant_pos : 0 < firstEliminationConstant := by
  unfold firstEliminationConstant
  exact mul_pos (mul_pos (mul_pos (mul_pos (pow_pos productBoundConstant_pos _) (by positivity))
    (pow_pos fewProductsFullConstant_pos _)) (by positivity)) (by positivity)
theorem secondEliminationConstant_pos : 0 < secondEliminationConstant := by
  unfold secondEliminationConstant
  exact mul_pos (mul_pos productBoundConstant_pos (by positivity)) (by positivity)
theorem sumProductConstant_pos : 0 < sumProductConstant := by
  unfold sumProductConstant
  exact mul_pos (mul_pos firstEliminationConstant_pos (pow_pos secondEliminationConstant_pos _)) (by positivity)

theorem guarded_sum_product_polynomial (A : Finset ℝ) (hA : Positive A) (hn : A.Nonempty)
    (hguard : 4608*((A+A).card : ℝ)^2*((A*A).card : ℝ)^2*(logBudget A.card : ℝ)^2 ≤ (A.card : ℝ)^6) :
    (A.card : ℝ)^1558 ≤ sumProductConstant*((A+A).card : ℝ)^694*
      ((A*A).card : ℝ)^473*(logBudget A.card : ℝ)^663 := by
  classical
  obtain ⟨s,τ,b,T,B,hs,hτ,hb,hT,hsn,hτn,he,hblock,hslice,hBn,hB,hBpos,hBsum,hrep,hprod⟩ :=
    exists_sum_product_structure A hA hn hguard
  have hP := positive_product hA hA
  have hAP : B.card ≤ (A*A).card := hBn.trans (card_le_product A hA)
  have hf := few_products B (A*A) T hB (fun z hz => ne_of_gt (hP z hz)) hAP hrep
  have hsum : ((B+B).card : ℝ) ≤ (A+A).card := by exact_mod_cast hBsum
  have hlog : (logBudget B.card : ℝ) ≤ logBudget A.card := by exact_mod_cast logBudget_mono hBn
  have hF0 := fewProductsFullConstant_pos.le
  have hf' : (B.card : ℝ)^41*(T : ℝ)^33 ≤
      fewProductsFullConstant*((A+A).card : ℝ)^19*((A*A).card : ℝ)^44*(logBudget A.card : ℝ)^24 := by
    calc
      _ ≤ fewProductsFullConstant*((A*A).card : ℝ)^44*((B+B).card : ℝ)^19*(logBudget B.card : ℝ)^24 := hf
      _ ≤ fewProductsFullConstant*((A*A).card : ℝ)^44*((A+A).card : ℝ)^19*(logBudget A.card : ℝ)^24 := by gcongr
      _ = _ := by ring
  obtain ⟨z,hz⟩ := hB
  have hTv : T ≤ (A*A).card := by
    have hh := hrep z hz
    rw [← slopeFiber_card (A*A) hP z] at hh
    exact hh.trans (slopeFiber_card_le (A*A) z)
  have hn0 : 0 < (A.card : ℝ) := by exact_mod_cast hn.card_pos
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast hs
  have hτ0 : 0 < (τ : ℝ) := by exact_mod_cast hτ
  have hslice' : (s : ℝ)*(τ : ℝ) ≤ 2*(A.card : ℝ)*(B.card : ℝ) := by exact_mod_cast hslice
  have h₁ := structure_first_elimination (A.card : ℝ) ((A+A).card : ℝ) ((A*A).card : ℝ)
    (logBudget A.card : ℝ) (s : ℝ) (τ : ℝ) (b : ℝ) (T : ℝ) (B.card : ℝ)
    productBoundConstant fewProductsFullConstant hn0 (by positivity) (by positivity) (by positivity)
    hs0 hτ0 (by positivity) (by positivity) (by positivity) productBoundConstant_pos.le hF0
    he hblock hslice' hprod hf'
  have h₂ := structure_second_elimination (A.card : ℝ) ((A+A).card : ℝ) ((A*A).card : ℝ)
    (logBudget A.card : ℝ) (s : ℝ) (τ : ℝ) (b : ℝ) (T : ℝ) productBoundConstant
    hn0 (by positivity) (by positivity) (by positivity) hs0 hτ0 (by positivity) (by positivity)
    productBoundConstant_pos.le (by exact_mod_cast hTv) he hblock hprod
  have h₃ : (A.card : ℝ)^4 ≤ 4*((s : ℝ)*(τ : ℝ)^2)*((A*A).card : ℝ)*(logBudget A.card : ℝ) := by
    nlinarith [he]
  exact raw_final_power (A.card : ℝ) ((A+A).card : ℝ) ((A*A).card : ℝ)
    (logBudget A.card : ℝ) (s : ℝ) ((s : ℝ)*(τ : ℝ)^2)
    firstEliminationConstant secondEliminationConstant hn0 (by positivity) (by positivity)
    (by positivity) hs0 (by positivity) firstEliminationConstant_pos.le secondEliminationConstant_pos.le h₁ h₂ h₃

end Erdos52.RSFresh

-- END RSProof/GlobalPolynomial.lean

-- BEGIN RSProof/LogAbsorption.lean

open Filter
namespace Erdos52.RSFresh

theorem logBudget_log_bound (n : ℕ) (hn : 2 ≤ n) :
    (logBudget n : ℝ)*Real.log 2 ≤ 5*Real.log (n : ℝ) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hp : (2 : ℝ)^(Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hh := Real.log_le_log (by positivity : 0 < (2 : ℝ)^(Nat.log 2 n)) hp
  rw [Real.log_pow] at hh
  have h2 : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  unfold logBudget
  push_cast
  linarith

theorem eventually_logBudget_pow_le (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (logBudget n : ℝ)^k ≤ (n : ℝ)^δ := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := (isLittleO_log_rpow_atTop (div_pos hδ hk')).bound
    (by positivity : 0 < Real.log 2 / 5)
  have hnat := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hsmall
  filter_upwards [hnat, eventually_ge_atTop 2] with n hn hn2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hnp : 0 ≤ (n : ℝ)^(δ/(k : ℝ)) := Real.rpow_nonneg hn0.le _
  simp only [Real.norm_eq_abs, abs_of_nonneg hnlog, abs_of_nonneg hnp] at hn
  have hb := logBudget_log_bound n hn2
  have hc : (logBudget n : ℝ) ≤ (n : ℝ)^(δ/(k : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (logBudget n : ℝ)) hc k
  have hid : ((n : ℝ)^(δ/(k : ℝ)))^k = (n : ℝ)^δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, div_mul_cancel₀ _ (ne_of_gt hk')]
  rwa [hid] at hp

end Erdos52.RSFresh

-- END RSProof/LogAbsorption.lean

-- BEGIN RSProof/PowerLogDomination.lean

open Filter
namespace Erdos52.RSFresh

theorem eventually_power_log_domination (a b C : ℝ) (hab : a < b) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, C*(n : ℝ)^a*(logBudget n : ℝ)^m ≤ (n : ℝ)^b := by
  let δ := (b-a)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlog := eventually_logBudget_pow_le (m+1) (by omega) δ hδ
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog,hlim.eventually_ge_atTop C,eventually_ge_atTop 1] with n hl hc hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : (1 : ℝ) ≤ logBudget n := by
    exact_mod_cast (show 1 ≤ logBudget n from logBudget_pos n)
  have hm := (pow_le_pow_right₀ hL (show m ≤ m+1 by omega)).trans hl
  calc
    C*(n : ℝ)^a*(logBudget n : ℝ)^m ≤
        (n : ℝ)^δ*(n : ℝ)^a*(n : ℝ)^δ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
      · exact hm
      · positivity
      · positivity
    _ = (n : ℝ)^(δ+a+δ) := by
      rw [Real.rpow_add hn0,Real.rpow_add hn0]
    _ = (n : ℝ)^b := by
      congr 1
      dsimp [δ]
      ring

end Erdos52.RSFresh

-- END RSProof/PowerLogDomination.lean

-- BEGIN RSProof/PositiveEndpoint.lean

open Filter
open scoped Pointwise
namespace Erdos52.RSFresh

theorem eventually_positive_sum_product (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ A : Finset ℝ, Positive A → N ≤ A.card →
      (A.card : ℝ)^((4 : ℝ)/3+2/1167-ε) ≤
        max ((A+A).card : ℝ) ((A*A).card : ℝ) := by
  let θ := (4 : ℝ)/3+2/1167-ε
  let β := (1167*θ+1558)/2
  have hθ : 4*θ < 6 := by dsimp [θ]; linarith
  have ha : 1167*θ < 1558 := by dsimp [θ]; linarith
  have hab : 1167*θ < β := by dsimp [β]; linarith
  have hb : β < 1558 := by dsimp [β]; linarith
  have hfirst := eventually_power_log_domination (4*θ) 6 4608 hθ 2
  have hsecond := eventually_power_log_domination (1167*θ) β sumProductConstant hab 663
  have hall : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 4608*(n : ℝ)^(4*θ)*(logBudget n : ℝ)^2 ≤ (n : ℝ)^(6 : ℝ) ∧
      sumProductConstant*(n : ℝ)^(1167*θ)*(logBudget n : ℝ)^663 ≤ (n : ℝ)^β := by
    filter_upwards [eventually_ge_atTop 2,hfirst,hsecond] with n hn h1 h2
    exact ⟨hn,h1,h2⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  refine ⟨max N 2,by omega,?_⟩
  intro A hA hn
  obtain ⟨hn2,hg,hf⟩ := hN A.card (by omega)
  have hn0 : 0 < (A.card : ℝ) := by exact_mod_cast (show 0 < A.card by omega)
  have hn1 : 1 < (A.card : ℝ) := by exact_mod_cast (show 1 < A.card by omega)
  have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
  by_contra hbad
  have hmax : max ((A+A).card : ℝ) ((A*A).card : ℝ) < (A.card : ℝ)^θ := lt_of_not_ge hbad
  have hu := (le_max_left ((A+A).card : ℝ) ((A*A).card : ℝ)).trans hmax.le
  have hv := (le_max_right ((A+A).card : ℝ) ((A*A).card : ℝ)).trans hmax.le
  have hpow (k : ℕ) : ((A.card : ℝ)^θ)^k = (A.card : ℝ)^((k : ℝ)*θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hfour : ((A.card : ℝ)^θ)^2*((A.card : ℝ)^θ)^2 = (A.card : ℝ)^(4*θ) := by
    calc
      _ = ((A.card : ℝ)^θ)^4 := by ring
      _ = _ := hpow 4
  have hguard : 4608*((A+A).card : ℝ)^2*((A*A).card : ℝ)^2*(logBudget A.card : ℝ)^2 ≤ (A.card : ℝ)^6 := by
    calc
      _ ≤ 4608*((A.card : ℝ)^θ)^2*((A.card : ℝ)^θ)^2*(logBudget A.card : ℝ)^2 := by gcongr
      _ = 4608*(A.card : ℝ)^(4*θ)*(logBudget A.card : ℝ)^2 := by rw [mul_assoc 4608, hfour]
      _ ≤ (A.card : ℝ)^(6 : ℝ) := hg
      _ = _ := Real.rpow_natCast _ 6
  have hp := guarded_sum_product_polynomial A hA hAn hguard
  have hup := pow_le_pow_left₀ (by positivity : 0 ≤ ((A+A).card : ℝ)) hu 694
  have hvp := pow_le_pow_left₀ (by positivity : 0 ≤ ((A*A).card : ℝ)) hv 473
  have hmul : ((A+A).card : ℝ)^694*((A*A).card : ℝ)^473 ≤ (A.card : ℝ)^(1167*θ) := by
    calc
      _ ≤ ((A.card : ℝ)^θ)^694*((A.card : ℝ)^θ)^473 :=
        mul_le_mul hup hvp (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.rpow_nonneg hn0.le _) _)
      _ = ((A.card : ℝ)^θ)^1167 := by rw [← pow_add]
      _ = _ := hpow 1167
  have hupper : (A.card : ℝ)^1558 ≤ (A.card : ℝ)^β := by
    calc
      _ ≤ sumProductConstant*((A+A).card : ℝ)^694*((A*A).card : ℝ)^473*(logBudget A.card : ℝ)^663 := hp
      _ = sumProductConstant*(((A+A).card : ℝ)^694*((A*A).card : ℝ)^473)*(logBudget A.card : ℝ)^663 := by ring
      _ ≤ sumProductConstant*(A.card : ℝ)^(1167*θ)*(logBudget A.card : ℝ)^663 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul sumProductConstant_pos.le)
          (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := hf
  have hstrict := Real.rpow_lt_rpow_of_exponent_lt hn1 hb
  have he1558 : (A.card : ℝ)^(1558 : ℝ) = (A.card : ℝ)^(1558 : ℕ) := Real.rpow_natCast _ 1558
  rw [he1558] at hstrict
  exact (not_lt_of_ge hupper) hstrict

end Erdos52.RSFresh

-- END RSProof/PositiveEndpoint.lean

-- BEGIN RSProof/PositiveReduction.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem exists_positive_part (A : Finset ℝ) (hn : 2 ≤ A.card) :
    ∃ B : Finset ℝ, Positive B ∧ A.card ≤ 3*B.card ∧
      (B+B).card ≤ (A+A).card ∧ (B*B).card ≤ (A*A).card := by
  classical
  let P := A.filter (fun x => 0 < x)
  let N := A.filter (fun x => x < 0)
  have hcover : A ⊆ P ∪ N ∪ {0} := by
    intro x hx
    by_cases hp : 0 < x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,hp⟩))
    by_cases hm : x < 0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,hm⟩))
    · exact Finset.mem_union_right _ (by simp; linarith)
  have hc : A.card ≤ P.card+N.card+1 := by
    have hh := Finset.card_le_card hcover
    have hu := Finset.card_union_le (P ∪ N) {0}
    have hv := Finset.card_union_le P N
    simp only [Finset.card_singleton] at hu
    omega
  have hpA : P ⊆ A := Finset.filter_subset _ _
  have hnA : N ⊆ A := Finset.filter_subset _ _
  by_cases hpn : N.card ≤ P.card
  · refine ⟨P,?_,by omega,?_,?_⟩
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · exact Finset.card_le_card (Finset.add_subset_add hpA hpA)
    · exact Finset.card_le_card (Finset.mul_subset_mul hpA hpA)
  · let B := N.image (fun x => -x)
    have hcard : B.card = N.card := Finset.card_image_of_injective N neg_injective
    refine ⟨B,?_,by omega,?_,?_⟩
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact neg_pos.mpr (Finset.mem_filter.mp hy).2
    · have hs : B+B ⊆ (A+A).image (fun x => -x) := by
        intro z hz
        obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨u+v,Finset.mem_add.mpr ⟨u,hnA hu,v,hnA hv,rfl⟩,by ring⟩
      exact (Finset.card_le_card hs).trans Finset.card_image_le
    · have hs : B*B ⊆ A*A := by
        intro z hz
        obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_mul.mp hz
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_mul.mpr ⟨u,hnA hu,v,hnA hv,by ring⟩
      exact Finset.card_le_card hs

end Erdos52.RSFresh

-- END RSProof/PositiveReduction.lean

-- BEGIN RSProof/FiniteRangeExtension.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem finite_range_extension (θ : ℝ) (hθ : 0 < θ) (N : ℕ) (hN : 1 ≤ N)
    (hevent : ∀ B : Finset ℝ, Positive B → N ≤ B.card →
      (B.card : ℝ)^θ ≤ max ((B+B).card : ℝ) ((B*B).card : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℝ,
      C*(A.card : ℝ)^θ ≤ max ((A+A).card : ℝ) ((A*A).card : ℝ) := by
  classical
  let D : ℝ := 3*(N:ℝ)+3
  have hD : 0 < D := by dsimp [D]; positivity
  have hp : 0 < D^θ := Real.rpow_pos_of_pos hD θ
  refine ⟨1/(D^θ),by positivity,?_⟩
  intro A
  by_cases ha : A.Nonempty
  · have hmax : (1:ℝ) ≤ max ((A+A).card : ℝ) ((A*A).card : ℝ) := by
      obtain ⟨a,ha⟩ := ha
      have hh : (A+A).Nonempty := ⟨a+a,Finset.mem_add.mpr ⟨a,ha,a,ha,rfl⟩⟩
      have hc : (1:ℝ) ≤ (A+A).card := by exact_mod_cast hh.card_pos
      exact hc.trans (le_max_left _ _)
    rw [one_div, mul_comm]
    change (A.card : ℝ)^θ / D^θ ≤ _
    apply (div_le_iff₀ hp).mpr
    by_cases hn : 3*N+3 ≤ A.card
    · obtain ⟨B,hB,hcard,hs,hm⟩ := exists_positive_part A (by omega)
      have hBN : N ≤ B.card := by omega
      have hBcard : (0:ℝ) ≤ B.card := by positivity
      have hcardr : (A.card:ℝ) ≤ 3*(B.card:ℝ) := by exact_mod_cast hcard
      have h3 : (3:ℝ) ≤ D := by dsimp [D]; have := Nat.cast_nonneg (α := ℝ) N; linarith
      have hsize : (A.card:ℝ) ≤ D*(B.card:ℝ) := hcardr.trans (mul_le_mul_of_nonneg_right h3 hBcard)
      have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ A.card) hsize hθ.le
      rw [Real.mul_rpow hD.le hBcard] at hh
      have hb := hevent B hB hBN
      have hs' : ((B+B).card:ℝ) ≤ (A+A).card := by exact_mod_cast hs
      have hm' : ((B*B).card:ℝ) ≤ (A*A).card := by exact_mod_cast hm
      have hu := hb.trans (max_le_max hs' hm')
      calc
        _ ≤ D^θ*(B.card:ℝ)^θ := hh
        _ ≤ D^θ*max ((A+A).card:ℝ) ((A*A).card:ℝ) := mul_le_mul_of_nonneg_left hu hp.le
        _ = _ := by ring
    · have hsize : (A.card:ℝ) ≤ D := by dsimp [D]; exact_mod_cast (by omega : A.card ≤ 3*N+3)
      have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ A.card) hsize hθ.le
      calc
        _ ≤ D^θ := hh
        _ ≤ max ((A+A).card:ℝ) ((A*A).card:ℝ)*D^θ := by nlinarith
  · have hz := Finset.not_nonempty_iff_eq_empty.mp ha
    subst A
    simp [Real.zero_rpow hθ.ne']

end Erdos52.RSFresh

-- END RSProof/FiniteRangeExtension.lean

-- BEGIN RSProof/IntegerTransfer.lean

open scoped Pointwise
namespace Erdos52.RSFresh

theorem integer_transfer (θ C : ℝ)
    (h : ∀ A : Finset ℝ, C*(A.card:ℝ)^θ ≤ max ((A+A).card:ℝ) ((A*A).card:ℝ)) :
    ∀ A : Finset ℤ, C*(A.card:ℝ)^θ ≤ max ((A+A).card:ℝ) ((A*A).card:ℝ) := by
  classical
  intro A
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have hf : Function.Injective f := by intro x y hxy; change (x:ℝ)=(y:ℝ) at hxy; exact_mod_cast hxy
  have hc (S : Finset ℤ) : (S.image f).card = S.card := Finset.card_image_of_injective S hf
  have hs : (A+A).image f = A.image f + A.image f := Finset.image_add f
  have hm : (A*A).image f = A.image f * A.image f := Finset.image_mul f
  have hh := h (A.image f)
  rw [← hs,← hm,hc A,hc (A+A),hc (A*A)] at hh
  exact hh

end Erdos52.RSFresh

-- END RSProof/IntegerTransfer.lean

-- BEGIN RSProof/NativeConclusion.lean

open scoped Pointwise
namespace Erdos52
theorem RSFresh.native_rudnev_stevens_exponent : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥
      C * (A.card : ℝ) ^ ((4 : ℝ) / 3 + 2 / 1167 - ε) := by
  intro ε hε hε1
  obtain ⟨N,hN,he⟩ := RSFresh.eventually_positive_sum_product ε hε hε1
  have hθ : 0 < (4:ℝ)/3+2/1167-ε := by linarith
  obtain ⟨C,hC,hbound⟩ := RSFresh.finite_range_extension _ hθ N hN he
  refine ⟨C,hC,?_⟩
  intro A
  have hh := RSFresh.integer_transfer _ C hbound A
  simpa only [Nat.cast_max] using hh
end Erdos52

-- END RSProof/NativeConclusion.lean

-- BEGIN RSProof/Canonical.lean

open scoped Pointwise
namespace Erdos52
theorem rudnev_stevens_exponent : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥
      C * (A.card : ℝ) ^ ((4 : ℝ) / 3 + 2 / 1167 - ε) := by exact RSFresh.native_rudnev_stevens_exponent
end Erdos52

-- END RSProof/Canonical.lean

open Erdos52

theorem solution : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥
      C * (A.card : ℝ) ^ ((4 : ℝ) / 3 + 2 / 1167 - ε) := by
  exact Erdos52.rudnev_stevens_exponent
