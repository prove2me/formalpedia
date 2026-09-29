-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_mem_holOn_hasProd_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9f079d71-1f08-5fb8-b2e9-45ab7144fe00

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "Filter Topology CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.RatPair Omega.holOn"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair RatPair.evalAt RatPair.const RatPair.mul RatPair.isPoleFreeOn_const RatPair.isPoleFreeOn_mul RatPair.evalAt_mul tendstoUniformly_iff_vRestrict holOn"
namespace UnifProd
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v : Valuation K Γ₀)

section Ultra

variable {ι : Type}

theorem v_eq_one_of_sub_one_lt {x : K} {g : Γ₀} (hg : g ≤ 1) (h : v (x - 1) < g) : v x = 1 := by
  have : v (x - 1) < v (1 : K) := by rw [Valuation.map_one]; exact h.trans_le hg
  rw [Valuation.map_eq_of_sub_lt _ this, Valuation.map_one]

theorem v_prod_sub_one_lt (s : Finset ι) (x : ι → K) {g : Γ₀} (hg : g ≤ 1) (hg0 : g ≠ 0)
    (h : ∀ i ∈ s, v (x i - 1) < g) : v (∏ i ∈ s, x i - 1) < g := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, sub_self, Valuation.map_zero]; exact zero_lt_iff.mpr hg0
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs : ∀ i ∈ s, v (x i - 1) < g := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 : v (∏ i ∈ s, x i - 1) < g := ih hs
    have h2 : v (∏ i ∈ s, x i) = 1 := v_eq_one_of_sub_one_lt hg h1
    have h3 : v (x a - 1) < g := h a (Finset.mem_insert_self a s)
    have : x a * ∏ i ∈ s, x i - 1 = (x a - 1) * ∏ i ∈ s, x i + (∏ i ∈ s, x i - 1) := by ring
    rw [this]
    apply Valuation.map_add_lt _ _ h1
    rw [Valuation.map_mul, h2, mul_one]
    exact h3

theorem v_prod_eq_one (s : Finset ι) (x : ι → K) {g : Γ₀} (hg : g ≤ 1) (hg0 : g ≠ 0)
    (h : ∀ i ∈ s, v (x i - 1) < g) : v (∏ i ∈ s, x i) = 1 :=
  v_eq_one_of_sub_one_lt hg (v_prod_sub_one_lt s x hg hg0 h)

end Ultra

section RatPairProd

noncomputable scoped instance instCommMonoidRatPair : CommMonoid (RatPair K) where
  mul := RatPair.mul
  one := RatPair.const 1
  mul_assoc p q r := by
    show RatPair.mul (RatPair.mul p q) r = RatPair.mul p (RatPair.mul q r)
    simp only [RatPair.mul, mul_assoc]
  one_mul p := by
    cases p
    show RatPair.mul (RatPair.const 1) _ = _
    simp [RatPair.mul, RatPair.const]
  mul_one p := by
    cases p
    show RatPair.mul _ (RatPair.const 1) = _
    simp [RatPair.mul, RatPair.const]
  mul_comm p q := by
    show RatPair.mul p q = RatPair.mul q p
    simp only [RatPair.mul, mul_comm]

variable {ι : Type}

theorem evalAt_one (z : K) : (1 : RatPair K).evalAt z = 1 := by
  show (RatPair.const 1).evalAt z = 1
  simp [RatPair.evalAt, RatPair.const]

theorem isPoleFreeOn_one (S : Set K) : (1 : RatPair K).IsPoleFreeOn S :=
  RatPair.isPoleFreeOn_const S 1

theorem evalAt_prod (s : Finset ι) (f : ι → RatPair K) (z : K) :
    (∏ i ∈ s, f i).evalAt z = ∏ i ∈ s, (f i).evalAt z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, evalAt_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
    exact RatPair.evalAt_mul _ _ z

theorem isPoleFreeOn_prod {S : Set K} (s : Finset ι) (f : ι → RatPair K) (hf : ∀ i, (f i).IsPoleFreeOn S) :
    (∏ i ∈ s, f i).IsPoleFreeOn S := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact isPoleFreeOn_one S
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact RatPair.isPoleFreeOn_mul (hf a) ih

end RatPairProd

section Thresholds

noncomputable def dmin (c : ℕ → K) : ℕ → K
  | 0 => c 0
  | n + 1 => if v (c (n + 1)) ≤ v (dmin c n) then c (n + 1) else dmin c n

theorem dmin_exists_eq (c : ℕ → K) : ∀ n, ∃ j, j ≤ n ∧ dmin c n = c j
  | 0 => ⟨0, le_rfl, rfl⟩
  | n + 1 => by
    simp only [dmin]
    split_ifs
    · exact ⟨n + 1, le_rfl, rfl⟩
    · obtain ⟨j, hj, h⟩ := dmin_exists_eq c n
      exact ⟨j, hj.trans (Nat.le_succ n), h⟩

theorem v_dmin_le (c : ℕ → K) : ∀ {j n : ℕ}, j ≤ n → v (dmin c n) ≤ v (c j) := by
  intro j n
  induction n with
  | zero => intro h; rw [Nat.le_zero.mp h]; exact le_rfl
  | succ n ih =>
    intro h
    simp only [dmin]
    rcases Nat.of_le_succ h with h' | h'
    · split_ifs with hle
      · exact hle.trans (ih h')
      · exact ih h'
    · subst h'
      split_ifs with hle
      · exact le_rfl
      · exact (le_of_not_ge hle)

theorem v_dmin_antitone (c : ℕ → K) {m n : ℕ} (h : m ≤ n) : v (dmin c n) ≤ v (dmin c m) := by
  obtain ⟨j, hj, hjm⟩ := dmin_exists_eq c m
  rw [hjm]
  exact v_dmin_le c (hj.trans h)

theorem dmin_ne_zero (c : ℕ → K) (hc : ∀ n, c n ≠ 0) (n : ℕ) : dmin c n ≠ 0 := by
  obtain ⟨j, -, h⟩ := dmin_exists_eq c n
  rw [h]; exact hc j

end Thresholds

theorem exists_restrict_eq (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation K Γ₀) : K →*₀ Γ₀))ˣ) :
    ∃ y : K, y ≠ 0 ∧ (Valued.v : Valuation K Γ₀).restrict y = (γ : MonoidWithZeroHom.ValueGroup₀ _) := by
  obtain ⟨y, hy⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ₀) : K →*₀ Γ₀) γ.1
  refine ⟨y, fun h => γ.ne_zero ?_, ?_⟩
  · rw [← hy, h, map_zero]
  · rw [Valuation.restrict_def]; exact hy

section Main

variable [CompleteSpace K] {S : Set K} {ι : Type}

theorem main (r : ι → RatPair K)
    (hpf : ∀ γ, (r γ).IsPoleFreeOn S)
    (hbd : ∀ γ, ∃ b : K, ∀ z ∈ S, Valued.v ((r γ).evalAt z) ≤ Valued.v b)
    (c : ℕ → K) (hc : ∀ n, c n ≠ 0) (hcof : ∀ y : K, y ≠ 0 → ∃ n, Valued.v (c n) ≤ Valued.v y)
    (E : ℕ → Finset ι) (hmono : Monotone E)
    (hE : ∀ n, ∀ γ, γ ∉ E n → ∀ z ∈ S, Valued.v ((r γ).evalAt z - 1) < Valued.v (c n)) :
    ∃ P : ↥S → K, P ∈ holOn K S ∧
      (∀ z : ↥S, HasProd (fun γ => (r γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥S, P z = 0 ↔ ∃ γ, (r γ).evalAt (z : K) = 0) := by
  classical

  choose b₀ hb₀ using hbd
  let b : ι → K := fun γ => if v (b₀ γ) ≤ 1 then 1 else b₀ γ
  have hb : ∀ γ, ∀ z ∈ S, v ((r γ).evalAt z) ≤ v (b γ) := by
    intro γ z hz
    simp only [b]
    split_ifs with h
    · rw [Valuation.map_one]; exact (hb₀ γ z hz).trans h
    · exact hb₀ γ z hz
  have hb1 : ∀ γ, 1 ≤ v (b γ) := by
    intro γ; simp only [b]; split_ifs with h
    · rw [Valuation.map_one]
    · exact (lt_of_not_ge h).le
  have hb0 : ∀ γ, b γ ≠ 0 := fun γ h => by
    have := hb1 γ; rw [h, Valuation.map_zero] at this; exact not_lt.mpr this zero_lt_one

  obtain ⟨n₁, hn₁⟩ := hcof 1 one_ne_zero
  let d : ℕ → K := fun k => dmin c (n₁ + k)
  have hd0 : ∀ k, d k ≠ 0 := fun k => dmin_ne_zero c hc _
  have hd1 : ∀ k, v (d k) ≤ 1 := fun k => by
    have := v_dmin_le c (show n₁ ≤ n₁ + k from Nat.le_add_right _ _)
    rw [Valuation.map_one] at hn₁
    exact this.trans hn₁
  have hdanti : ∀ {k m : ℕ}, k ≤ m → v (d m) ≤ v (d k) := fun h => v_dmin_antitone c (Nat.add_le_add_left h _)
  have hdcof : ∀ y : K, y ≠ 0 → ∃ k, v (d k) ≤ v y := by
    intro y hy
    obtain ⟨n, hn⟩ := hcof y hy
    refine ⟨n, (v_dmin_le c (show n ≤ n₁ + n from Nat.le_add_left _ _)).trans hn⟩
  let E' : ℕ → Finset ι := fun k => E (n₁ + k)
  have hE'mono : ∀ {k m : ℕ}, k ≤ m → E' k ⊆ E' m := fun h => hmono (Nat.add_le_add_left h _)
  have hE' : ∀ k γ, γ ∉ E' k → ∀ z ∈ S, v ((r γ).evalAt z - 1) < v (d k) := by
    intro k γ hγ z hz
    obtain ⟨j, hj, hjd⟩ := dmin_exists_eq c (n₁ + k)
    show v ((r γ).evalAt z - 1) < v (dmin c (n₁ + k))
    rw [hjd]
    exact hE j γ (fun h => hγ (hmono hj h)) z hz

  let Q : ℕ → RatPair K := fun k => ∏ γ ∈ E' k, r γ
  let q : ℕ → K → K := fun k z => ∏ γ ∈ E' k, (r γ).evalAt z
  have hQq : ∀ k z, (Q k).evalAt z = q k z := fun k z => evalAt_prod _ _ _
  let B : K := ∏ γ ∈ E' 0, b γ
  have hB0 : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun γ _ => hb0 γ
  have hBpos : 0 < v B := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hB0)

  have tail : ∀ {k : ℕ} {t : Finset ι}, E' k ⊆ t → ∀ z ∈ S,
      (∏ γ ∈ t, (r γ).evalAt z) = q k z * ∏ γ ∈ t \ E' k, (r γ).evalAt z ∧
      v (∏ γ ∈ t \ E' k, (r γ).evalAt z - 1) < v (d k) := by
    intro k t ht z hz
    refine ⟨by rw [mul_comm]; exact (Finset.prod_sdiff ht).symm, ?_⟩
    exact v_prod_sub_one_lt _ _ (hd1 k) ((Valuation.ne_zero_iff _).mpr (hd0 k))
      (fun γ hγ => hE' k γ (Finset.mem_sdiff.mp hγ).2 z hz)
  have hqv : ∀ k, ∀ z ∈ S, v (q k z) = v (q 0 z) := by
    intro k z hz
    obtain ⟨h1, h2⟩ := tail (hE'mono (Nat.zero_le k)) z hz
    show v (∏ γ ∈ E' k, (r γ).evalAt z) = v (q 0 z)
    rw [h1, Valuation.map_mul, v_eq_one_of_sub_one_lt (hd1 0) h2, mul_one]
  have hqB : ∀ k, ∀ z ∈ S, v (q k z) ≤ v B := by
    intro k z hz
    rw [hqv k z hz]
    show v (∏ γ ∈ E' 0, (r γ).evalAt z) ≤ v (∏ γ ∈ E' 0, b γ)
    rw [map_prod, map_prod]
    exact Finset.prod_le_prod' fun γ _ => hb γ z hz

  have cauchy : ∀ {k m : ℕ}, k ≤ m → ∀ z ∈ S, v (q m z - q k z) < v (B * d k) := by
    intro k m hkm z hz
    obtain ⟨h1, h2⟩ := tail (hE'mono hkm) z hz
    have : q m z - q k z = q k z * (∏ γ ∈ E' m \ E' k, (r γ).evalAt z - 1) := by
      show (∏ γ ∈ E' m, (r γ).evalAt z) - q k z = _
      rw [h1]; ring
    rw [this, Valuation.map_mul, Valuation.map_mul]
    calc v (q k z) * v (∏ γ ∈ E' m \ E' k, (r γ).evalAt z - 1)
        ≤ v B * v (∏ γ ∈ E' m \ E' k, (r γ).evalAt z - 1) := mul_le_mul_left (hqB k z hz) _
      _ < v B * v (d k) := mul_lt_mul_of_pos_left h2 hBpos

  have hCauchy : ∀ z ∈ S, CauchySeq (fun k => q k z) := by
    intro z hz
    rw [(Valued.hasBasis_uniformity K Γ₀).cauchySeq_iff]
    intro γ _
    obtain ⟨y, hy0, hy⟩ := exists_restrict_eq γ
    obtain ⟨k₀, hk₀⟩ := hdcof (y / B) (div_ne_zero hy0 hB0)
    refine ⟨k₀, fun m hm n hn => ?_⟩
    show Valued.v.restrict (q n z - q m z) < γ.1
    have hbd' : v (B * d k₀) ≤ v y := by
      rw [Valuation.map_mul]
      calc v B * v (d k₀) ≤ v B * v (y / B) := mul_le_mul_right hk₀ _
        _ = v y := by rw [← Valuation.map_mul, mul_div_cancel₀ _ hB0]
    have e1 : v (q n z - q k₀ z) < v y := (cauchy hn z hz).trans_le hbd'
    have e2 : v (q m z - q k₀ z) < v y := (cauchy hm z hz).trans_le hbd'
    have : q n z - q m z = (q n z - q k₀ z) - (q m z - q k₀ z) := by ring
    rw [← hy, Valuation.restrict_lt_iff, this]
    exact Valuation.map_sub_lt _ e1 e2
  choose! P hP using fun z (hz : z ∈ S) => cauchySeq_tendsto_of_complete (hCauchy z hz)

  have limit_bd : ∀ k, ∀ z ∈ S, v (P z - q k z) < v (B * d k) := by
    intro k z hz
    have hclosed : IsClosed {x : K | Valued.v.restrict (x - q k z) < Valued.v.restrict (B * d k)} :=
      (Valued.isClosed_ball K (Valued.v.restrict (B * d k))).preimage (continuous_id.sub continuous_const)
    have hmem : ∀ᶠ m in atTop, q m z ∈ {x : K | Valued.v.restrict (x - q k z) < Valued.v.restrict (B * d k)} :=
      Filter.eventually_atTop.mpr ⟨k, fun m hm => by
        show Valued.v.restrict (q m z - q k z) < Valued.v.restrict (B * d k)
        rw [Valuation.restrict_lt_iff]; exact cauchy hm z hz⟩
    have := hclosed.mem_of_tendsto (hP z hz) hmem
    rwa [Set.mem_setOf_eq, Valuation.restrict_lt_iff] at this

  refine ⟨fun z => P z, ?_, ?_, ?_⟩
  ·
    refine ⟨Q, fun k => isPoleFreeOn_prod _ _ hpf, ⟨B, fun k z => by rw [hQq]; exact hqB k z z.2⟩, ?_⟩
    rw [tendstoUniformly_iff_vRestrict]
    intro γ
    obtain ⟨y, hy0, hy⟩ := exists_restrict_eq γ
    obtain ⟨k₀, hk₀⟩ := hdcof (y / B) (div_ne_zero hy0 hB0)
    refine Filter.eventually_atTop.mpr ⟨k₀, fun k hk z => ?_⟩
    show Valued.v.restrict ((Q k).evalAt z - P z) < γ.1
    rw [← hy, Valuation.restrict_lt_iff, hQq, ← Valuation.map_neg, neg_sub]
    calc v (P z - q k z) < v (B * d k) := limit_bd k z z.2
      _ ≤ v (B * d k₀) := by rw [Valuation.map_mul, Valuation.map_mul]; exact mul_le_mul_right (hdanti hk) _
      _ ≤ v y := by
        rw [Valuation.map_mul]
        calc v B * v (d k₀) ≤ v B * v (y / B) := mul_le_mul_right hk₀ _
          _ = v y := by rw [← Valuation.map_mul, mul_div_cancel₀ _ hB0]
  ·
    intro z
    rw [HasProd, Filter.tendsto_def]
    intro s hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
    obtain ⟨y, hy0, hy⟩ := exists_restrict_eq γ
    obtain ⟨k₀, hk₀⟩ := hdcof (y / B) (div_ne_zero hy0 hB0)
    have hbd' : v (B * d k₀) ≤ v y := by
      rw [Valuation.map_mul]
      calc v B * v (d k₀) ≤ v B * v (y / B) := mul_le_mul_right hk₀ _
        _ = v y := by rw [← Valuation.map_mul, mul_div_cancel₀ _ hB0]
    refine Filter.mem_atTop_sets.mpr ⟨E' k₀, fun t ht => ?_⟩
    show (∏ γ ∈ t, (r γ).evalAt (z : K)) ∈ s
    apply hγ
    show Valued.v.restrict ((∏ γ ∈ t, (r γ).evalAt (z : K)) - P z) < γ.1
    rw [← hy, Valuation.restrict_lt_iff]
    obtain ⟨h1, h2⟩ := tail ht z z.2
    have e1 : v ((∏ γ ∈ t, (r γ).evalAt (z : K)) - q k₀ z) < v (B * d k₀) := by
      have : (∏ γ ∈ t, (r γ).evalAt (z : K)) - q k₀ z = q k₀ z * (∏ γ ∈ t \ E' k₀, (r γ).evalAt z - 1) := by
        rw [h1]; ring
      rw [this, Valuation.map_mul, Valuation.map_mul]
      calc v (q k₀ z) * v (∏ γ ∈ t \ E' k₀, (r γ).evalAt z - 1)
          ≤ v B * v (∏ γ ∈ t \ E' k₀, (r γ).evalAt z - 1) := mul_le_mul_left (hqB k₀ z z.2) _
        _ < v B * v (d k₀) := mul_lt_mul_of_pos_left h2 hBpos
    have e2 : v (P z - q k₀ z) < v (B * d k₀) := limit_bd k₀ z z.2
    have : (∏ γ ∈ t, (r γ).evalAt (z : K)) - P z = ((∏ γ ∈ t, (r γ).evalAt (z : K)) - q k₀ z) - (P z - q k₀ z) := by
      ring
    rw [this]
    exact (Valuation.map_sub_lt _ e1 e2).trans_le hbd'
  ·
    intro z
    constructor
    · intro hPz
      by_contra hne
      push Not at hne
      have hq0 : q 0 z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun γ _ => hne γ
      obtain ⟨k, hk⟩ := hdcof (q 0 z / B) (div_ne_zero hq0 hB0)
      have hbd' : v (B * d k) ≤ v (q k z) := by
        rw [Valuation.map_mul, hqv k z z.2]
        calc v B * v (d k) ≤ v B * v (q 0 z / B) := mul_le_mul_right hk _
          _ = v (q 0 z) := by rw [← Valuation.map_mul, mul_div_cancel₀ _ hB0]
      have h1 : v (P z - q k z) < v (q k z) := (limit_bd k z z.2).trans_le hbd'
      have h2 : v (P z) = v (q k z) := Valuation.map_eq_of_sub_lt _ h1
      rw [show P z = 0 from hPz, Valuation.map_zero, hqv k z z.2] at h2
      exact hq0 ((Valuation.zero_iff _).mp h2.symm)
    · rintro ⟨γ₀, hγ₀⟩

      have hin : ∃ k, γ₀ ∈ E' k := by
        by_contra hout
        push Not at hout
        have hsmall : ∀ k, v ((r γ₀).evalAt z - 1) < v (d k) := fun k => hE' k γ₀ (hout k) z z.2
        have h10 : (r γ₀).evalAt (z : K) - 1 ≠ 0 := by rw [hγ₀, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
        obtain ⟨k, hk⟩ := hdcof _ h10
        exact (lt_irrefl _) ((hsmall k).trans_le hk)
      obtain ⟨k, hk⟩ := hin
      have hqz : ∀ m, k ≤ m → q m z = 0 := fun m hm =>
        Finset.prod_eq_zero (hE'mono hm hk) hγ₀
      have hlim : Tendsto (fun m => q m z) atTop (𝓝 0) :=
        tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨k, fun m hm => (hqz m hm).symm⟩)
      exact tendsto_nhds_unique (hP z z.2) hlim

end Main

end CerednikDrinfeld.Omega.UnifProd
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld.Omega.UnifProd"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld.Omega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.CerednikDrinfeld"

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    {S : Set K} {ι : Type} (r : ι → CerednikDrinfeld.Omega.RatPair K)
    (hpf : ∀ γ, (r γ).IsPoleFreeOn S)
    (hbd : ∀ γ, ∃ b : K, ∀ z ∈ S, Valued.v ((r γ).evalAt z) ≤ Valued.v b)
    (c : ℕ → K) (hc : ∀ n, c n ≠ 0) (hcof : ∀ y : K, y ≠ 0 → ∃ n, Valued.v (c n) ≤ Valued.v y)
    (E : ℕ → Finset ι) (hmono : Monotone E)
    (hE : ∀ n, ∀ γ, γ ∉ E n → ∀ z ∈ S, Valued.v ((r γ).evalAt z - 1) < Valued.v (c n)) :
    ∃ P : ↥S → K, P ∈ CerednikDrinfeld.Omega.holOn K S ∧
      (∀ z : ↥S, HasProd (fun γ => (r γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥S, P z = 0 ↔ ∃ γ, (r γ).evalAt (z : K) = 0) :=
  CerednikDrinfeld.Omega.UnifProd.main r hpf hbd c hc hcof E hmono hE

end S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt (solution)
