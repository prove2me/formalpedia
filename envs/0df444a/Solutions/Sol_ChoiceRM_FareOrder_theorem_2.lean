-- Prove2me | solution 1 for ChoiceRM.FareOrder.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T00:59:41.406117+00:00
-- url     : https://prove2.me/submissions/cb422bb4-c33f-4d20-9e73-3fb152368ec6

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me c5980f75-c8f0-4181-8464-0abf496e2a32.
-- New complete proof using geometric separation and finite summation by parts.
import Definitions.Def_ChoiceRM_FareOrder_FareOrder
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE MajorizationSet
section
set_option autoImplicit false
namespace ChoiceRM.FareOrder.Proof
open Finset
variable {n : ℕ}

def prefixSum (i : ℕ) (y : Fin n → ℝ) : ℝ := ∑ j ∈ univ.filter (fun j : Fin n => j.val < i), y j

def majorizing (b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, i < n → prefixSum i b ≤ prefixSum i y) ∧ ∑ j, y j = ∑ j, b j}

lemma mem_majorizing_self (b : Fin n → ℝ) : b ∈ majorizing b := by
  exact ⟨fun _ _ => le_rfl, rfl⟩

lemma prefix_add (i : ℕ) (u v : Fin n → ℝ) : prefixSum i (u+v) = prefixSum i u + prefixSum i v := by
  simp [prefixSum, sum_add_distrib]
lemma prefix_smul (i : ℕ) (a : ℝ) (u : Fin n → ℝ) : prefixSum i (a • u) = a * prefixSum i u := by
  simp [prefixSum, mul_sum]
lemma prefix_single (k : ℕ) (i : Fin n) (a : ℝ) :
    prefixSum k (Pi.single i a) = if i.val < k then a else 0 := by
  classical
  simp [prefixSum, Pi.single_apply, eq_comm]

lemma majorizing_convex (b : Fin n → ℝ) : Convex ℝ (majorizing b) := by
  intro u hu v hv a c ha hc hac
  constructor
  · intro i hi
    rw [prefix_add, prefix_smul, prefix_smul]
    have h1 := mul_le_mul_of_nonneg_left (hu.1 i hi) ha
    have h2 := mul_le_mul_of_nonneg_left (hv.1 i hi) hc
    calc
      prefixSum i b = a * prefixSum i b + c * prefixSum i b := by rw [← add_mul, hac, one_mul]
      _ ≤ a * prefixSum i u + c * prefixSum i v := add_le_add h1 h2
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    rw [hu.2,hv.2,← add_mul,hac,one_mul]

lemma majorizing_closed (b : Fin n → ℝ) : IsClosed (majorizing b) := by
  have hc : ∀ i : ℕ, Continuous (prefixSum (n:=n) i) := by
    intro i
    unfold prefixSum
    fun_prop
  have ht : Continuous (fun y : Fin n → ℝ => ∑ j, y j) := by fun_prop
  have hh := (isClosed_iInter (fun i : ℕ => isClosed_iInter (fun _hi : i < n =>
    isClosed_le (continuous_const (y := prefixSum i b)) (hc i)))).inter (isClosed_eq ht (continuous_const (y := ∑ j, b j)))
  simpa only [majorizing, Set.ofPred_and, Set.ofPred_forall] using hh

lemma majorizing_ray (b : Fin n → ℝ) (i j : Fin n) (hij : i < j) (r : ℝ) (hr : 0 ≤ r) :
    b + r • (Pi.single i 1 - Pi.single j 1) ∈ majorizing b := by
  constructor
  · intro k _hk
    rw [prefix_add, prefix_smul]
    have he : prefixSum k (Pi.single i (1:ℝ) - Pi.single j 1) =
        (if i.val < k then 1 else 0) - (if j.val < k then 1 else 0) := by
      simp only [prefixSum, Pi.sub_apply, sum_sub_distrib]
      change prefixSum k (Pi.single i 1) - prefixSum k (Pi.single j 1) = _
      rw [prefix_single, prefix_single]
    rw [he]
    by_cases hi : i.val < k <;> by_cases hj : j.val < k
    · simp [hi,hj]
    · simp [hi,hj,hr]
    · exact False.elim (hi (lt_trans hij hj))
    · simp [hi,hj]
  · simp [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, sum_add_distrib, ← mul_sum,
      sum_sub_distrib]
end ChoiceRM.FareOrder.Proof
end
-- END MODULE MajorizationSet

-- BEGIN MODULE MixtureSeparation
section
set_option autoImplicit false
namespace ChoiceRM.FareOrder.Proof
open Finset
variable {n : ℕ}

lemma functional_eq_dot (L : (Fin n → ℝ) →L[ℝ] ℝ) (y : Fin n → ℝ) :
    L y = (fun i => L (Pi.single i 1)) ⬝ᵥ y := by
  classical
  have hy : y = ∑ i : Fin n, y i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hy, map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  apply sum_congr rfl
  intro i _
  rw [mul_comm]

lemma separator_antitone (b : Fin n → ℝ) (L : (Fin n → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hL : ∀ y ∈ majorizing b, c < L y) : Antitone (fun i => L (Pi.single i 1)) := by
  intro i j hij
  by_cases he : i = j
  · subst j; exact le_rfl
  have hij' : i < j := lt_of_le_of_ne hij he
  by_contra hn
  have hd : 0 < L (Pi.single j 1) - L (Pi.single i 1) := sub_pos.mpr (lt_of_not_ge hn)
  have hb := hL b (mem_majorizing_self b)
  let r : ℝ := (L b - c + 1) / (L (Pi.single j 1) - L (Pi.single i 1))
  have hr : 0 ≤ r := div_nonneg (by linarith) hd.le
  have hh := hL _ (majorizing_ray b i j hij' r hr)
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hh
  have heq : r * (L (Pi.single j 1) - L (Pi.single i 1)) = L b - c + 1 := by
    exact div_mul_cancel₀ _ hd.ne'
  nlinarith

lemma exists_majorizing_hull {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℝ) (b : Fin n → ℝ)
    (h : ∀ x : Fin n → ℝ, Antitone x → ∃ k, x ⬝ᵥ b ≤ x ⬝ᵥ a k) :
    ∃ y ∈ convexHull ℝ (Set.range a), y ∈ majorizing b := by
  by_contra hn
  have hd : Disjoint (convexHull ℝ (Set.range a)) (majorizing b) := by
    rw [Set.disjoint_left]
    intro y hy hb
    exact hn ⟨y,hy,hb⟩
  obtain ⟨L,u,v,hK,huv,hC⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ _) ((Set.finite_range a).isCompact_convexHull ℝ)
    (majorizing_convex b) (majorizing_closed b) hd
  obtain ⟨k,hk⟩ := h (fun i => L (Pi.single i 1)) (separator_antitone b L v hC)
  have ha := hK (a k) (subset_convexHull ℝ _ (Set.mem_range_self k))
  have hb := hC b (mem_majorizing_self b)
  rw [← functional_eq_dot L b, ← functional_eq_dot L (a k)] at hk
  linarith

lemma exists_majorizing_mixture {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℝ) (b : Fin n → ℝ)
    (h : ∀ x : Fin n → ℝ, Antitone x → ∃ k, x ⬝ᵥ b ≤ x ⬝ᵥ a k) :
    ∃ α : ι → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
      (∑ k, α k • a k) ∈ majorizing b := by
  classical
  obtain ⟨y,hy,hb⟩ := exists_majorizing_hull a b h
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s,w,hw,hs,he⟩ := hy
  let α : ι → ℝ := fun k => if k ∈ s then w k else 0
  refine ⟨α, ?_, ?_, ?_⟩
  · intro k
    dsimp [α]
    split_ifs with hk
    · exact hw k hk
    · exact le_rfl
  · simpa [α] using hs
  · have he' : ∑ k, α k • a k = y := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at he
      simpa [α, ite_smul] using he
    rw [he']
    exact hb
end ChoiceRM.FareOrder.Proof
end
-- END MODULE MixtureSeparation

-- BEGIN MODULE ChoiceValues
section

namespace ChoiceRM.FareOrder.Proof
open scoped BigOperators

lemma fareValue_eq_dot {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hsupp : SupportedOn P) (x : Fin n → ℝ) (S : Finset (Fin n)) :
    fareValue P x S = x ⬝ᵥ P S := by
  unfold fareValue dotProduct
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  rw [hsupp S j hj,mul_zero]

lemma dot_mixProb {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (α : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ mixProb P α = ∑ k, α k * (x ⬝ᵥ P (complete n k.val)) := by
  unfold dotProduct mixProb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ChoiceRM.FareOrder.Proof
end
-- END MODULE ChoiceValues

-- BEGIN MODULE Necessity
section
set_option autoImplicit false
namespace ChoiceRM.FareOrder.Proof

lemma nesting_gives_mixture {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hsupp : SupportedOn P) (h : HasFareOrderNesting P) (T : Finset (Fin n)) :
    ∃ α : Fin (n+1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
      (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
      ∑ j, mixProb P α j = ∑ j, P T j := by
  have hd : ∀ x : Fin n → ℝ, Antitone x →
      ∃ k : Fin (n+1), x ⬝ᵥ P T ≤ x ⬝ᵥ P (complete n k.val) := by
    intro x hx
    obtain ⟨k,hk,hmax⟩ := h.2 x hx
    refine ⟨⟨k, by omega⟩, ?_⟩
    simpa only [fareValue_eq_dot P hsupp] using hmax T
  obtain ⟨α,hα,hs,hm⟩ := exists_majorizing_mixture (fun k : Fin (n+1) => P (complete n k.val)) (P T) hd
  have he : (∑ k : Fin (n+1), α k • P (complete n k.val)) = mixProb P α := by
    ext j
    simp [mixProb]
  rw [he] at hm
  exact ⟨α,hα,hs,hm⟩
end ChoiceRM.FareOrder.Proof
end
-- END MODULE Necessity

-- BEGIN MODULE PrefixOrder
section

namespace ChoiceRM.FareOrder.Proof
open scoped BigOperators

lemma prefixSum_castSucc {n : ℕ} (d : Fin (n+1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    prefixSum k d = prefixSum k (fun i : Fin n => d i.castSucc) := by
  unfold prefixSum
  rw [Finset.sum_filter,Fin.sum_univ_castSucc,Finset.sum_filter]
  simp [show ¬ n < k from not_lt.mpr hk]

lemma prefixSum_full {n : ℕ} (d : Fin n → ℝ) : prefixSum n d = ∑ i, d i := by
  simp [prefixSum]

lemma weighted_prefix_lower (n : ℕ) (x d : Fin (n+1) → ℝ) (hx : Antitone x)
    (hd : ∀ k, k < n+1 → 0 ≤ prefixSum k d) :
    x (Fin.last n) * (∑ i, d i) ≤ ∑ i, x i * d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    let x' : Fin (n+1) → ℝ := fun i => x i.castSucc
    let d' : Fin (n+1) → ℝ := fun i => d i.castSucc
    have hx' : Antitone x' := fun i j hij => hx (by exact hij)
    have hd' : ∀ k, k < n+1 → 0 ≤ prefixSum k d' := by
      intro k hk
      have hp := hd k (by omega)
      rw [prefixSum_castSucc d k (by omega)] at hp
      exact hp
    have hi := ih x' d' hx' hd'
    have hs : 0 ≤ ∑ i, d' i := by
      have hp := hd (n+1) (by omega)
      rw [prefixSum_castSucc d (n+1) le_rfl] at hp
      simpa only [prefixSum_full] using hp
    have hlast : x (Fin.last (n+1)) ≤ x' (Fin.last n) := hx (Fin.le_last _)
    have hm := mul_le_mul_of_nonneg_right hlast hs
    conv_lhs => rw [Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    change x (Fin.last (n+1)) * ((∑ i, d' i) + d (Fin.last (n+1))) ≤
      (∑ i, x' i * d' i) + x (Fin.last (n+1)) * d (Fin.last (n+1))
    nlinarith

lemma weighted_sum_nonneg_of_prefix {n : ℕ} (x d : Fin n → ℝ) (hx : Antitone x)
    (hd : ∀ k, k < n → 0 ≤ prefixSum k d) (ht : ∑ i, d i = 0) :
    0 ≤ ∑ i, x i * d i := by
  cases n with
  | zero => simp
  | succ n =>
    have h := weighted_prefix_lower n x d hx hd
    simpa [ht] using h

lemma dot_le_of_majorizing {n : ℕ} (b y x : Fin n → ℝ)
    (hy : y ∈ majorizing b) (hx : Antitone x) : x ⬝ᵥ b ≤ x ⬝ᵥ y := by
  have hp : ∀ k, k < n → 0 ≤ prefixSum k (y-b) := by
    intro k hk
    have h := hy.1 k hk
    simpa [prefixSum,Finset.sum_sub_distrib] using sub_nonneg.mpr h
  have ht : ∑ i, (y-b) i = 0 := by
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,hy.2,sub_self]
  have h := weighted_sum_nonneg_of_prefix x (y-b) hx hp ht
  have he : (∑ i, x i * (y-b) i) = x ⬝ᵥ y - x ⬝ᵥ b := by
    simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,dotProduct]
  rw [he] at h
  linarith

end ChoiceRM.FareOrder.Proof
end
-- END MODULE PrefixOrder

-- BEGIN MODULE Sufficiency
section

namespace ChoiceRM.FareOrder.Proof
open scoped BigOperators

lemma nesting_optimal_of_majorization {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hsupp : SupportedOn P)
    (hmajor : ∀ T : Finset (Fin n), ¬ IsComplete T →
      ∃ α : Fin (n+1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
        (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
          ∑ j, mixProb P α j = ∑ j, P T j) :
    ∀ x : Fin n → ℝ, Antitone x →
      ∃ k ≤ n, ∀ S : Finset (Fin n), fareValue P x S ≤ fareValue P x (complete n k) := by
  intro x hx
  obtain ⟨k,_,hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n+1)))
    (fun k => fareValue P x (complete n k.val)) Finset.univ_nonempty
  refine ⟨k.val,by omega,fun S => ?_⟩
  by_cases hS : IsComplete S
  · obtain ⟨l,hl,rfl⟩ := hS
    exact hk ⟨l,by omega⟩ (Finset.mem_univ _)
  · obtain ⟨α,hα,hαsum,hpre,htot⟩ := hmajor S hS
    have hmem : mixProb P α ∈ majorizing (P S) := ⟨hpre,htot⟩
    calc
      fareValue P x S = x ⬝ᵥ P S := fareValue_eq_dot P hsupp x S
      _ ≤ x ⬝ᵥ mixProb P α := dot_le_of_majorizing _ _ x hmem hx
      _ = ∑ l, α l * fareValue P x (complete n l.val) := by
        rw [dot_mixProb]
        exact Finset.sum_congr rfl fun l _ => congrArg (fun v => α l * v)
          (fareValue_eq_dot P hsupp x (complete n l.val)).symm
      _ ≤ ∑ l, α l * fareValue P x (complete n k.val) :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hk l (Finset.mem_univ _)) (hα l)
      _ = fareValue P x (complete n k.val) := by
        rw [← Finset.sum_mul,hαsum,one_mul]

end ChoiceRM.FareOrder.Proof
end
-- END MODULE Sufficiency

-- BEGIN MODULE FullCharacterization
section

namespace ChoiceRM.FareOrder

open RevenueManagement

/-- Theorem 2, p. 19: a choice model has the nested-by-fare-order property iff (i) the purchase
probability `Q` is increasing and (ii) for every incomplete set `T` some convex combination
`P̄(α)` of the complete sets majorizes `(P_1(T), …, P_n(T))`. -/
theorem theorem_2 {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) :
    HasFareOrderNesting P ↔
      ((∀ S T : Finset (Fin n), S ⊆ T → purchaseProb P S ≤ purchaseProb P T) ∧
        ∀ T : Finset (Fin n), ¬ IsComplete T →
          ∃ α : Fin (n + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
            (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
            ∑ j, mixProb P α j = ∑ j, P T j) := by
  have _hmodel := hP
  constructor
  · intro h
    exact ⟨h.1, fun T _hT => Proof.nesting_gives_mixture P hsupp h T⟩
  · rintro ⟨hQ,hmajor⟩
    exact ⟨hQ, Proof.nesting_optimal_of_majorization P hsupp hmajor⟩

end ChoiceRM.FareOrder

end
-- END MODULE FullCharacterization

-- BEGIN MODULE PublicSolution
section
open RevenueManagement ChoiceRM.FareOrder

theorem solution {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) :
    HasFareOrderNesting P ↔
      ((∀ S T : Finset (Fin n), S ⊆ T → purchaseProb P S ≤ purchaseProb P T) ∧
        ∀ T : Finset (Fin n), ¬ IsComplete T →
          ∃ α : Fin (n + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
            (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
            ∑ j, mixProb P α j = ∑ j, P T j) := by
  exact ChoiceRM.FareOrder.theorem_2 P hP hsupp


end
-- END MODULE PublicSolution

#print axioms ChoiceRM.FareOrder.theorem_2
#print axioms solution
