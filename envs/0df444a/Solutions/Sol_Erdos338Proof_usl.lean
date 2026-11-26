-- Prove2me | solution 1 for Erdos338Proof.usl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:04.242106+00:00
-- url     : https://prove2.me/submissions/11559124-0ae3-4504-b13a-5dbf1b99028a

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Shift
public import Theorems.Thm_Erdos338Proof_cnt_le_of_subset
public import Theorems.Thm_Erdos338Proof_cover


set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, ∀ M : Set ℕ, (∃ N, ∀ b ≥ N, γ * b ≤ cnt M b) →
    ∃ d b₀ N', 1 ≤ d ∧ d ≤ K ∧ ∀ x ≥ N', ∃ Ms : Multiset ℕ, Multiset.card Ms = K ∧
      (∀ a ∈ Ms, a ∈ M) ∧ Ms.sum = K * b₀ + d * x := by
  classical
  obtain ⟨K, hK, hcov⟩ := cover (half_pos hγ)
  have hγK : 4 < K * γ := by
    have e : (2 / (γ / 2) : ℝ) = 4 / γ := by field_simp; norm_num
    rw [e, div_lt_iff₀ hγ] at hK
    exact hK
  refine ⟨K, fun M ⟨N, hN⟩ ↦ ?_⟩
  -- `M` is infinite
  have hlarge : ∀ y, ∃ x ∈ M, y ≤ x := by
    intro y
    by_contra hcon
    push Not at hcon
    set b := N + ⌈((y : ℝ) + 1) / γ⌉₊ with hb
    have h1 := hN b (by omega)
    have h2 : cnt M b ≤ y := cnt_le_of_subset fun x hx _ ↦ hcon x hx
    have h3 : ((y : ℝ) + 1) / γ ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈((y : ℝ) + 1) / γ⌉₊ ≤ b))
    have h4 : (y : ℝ) + 1 ≤ γ * b := by rwa [div_le_iff₀ hγ, mul_comm] at h3
    have h5 : (cnt M b : ℝ) ≤ y := by exact_mod_cast h2
    linarith
  obtain ⟨b₀, hb₀, -⟩ := hlarge 0
  set D : Set ℕ := {u | b₀ + u ∈ M} with hD
  set I := Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' D) with hI
  have hex : ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ I := by
    obtain ⟨x, hx, hxb⟩ := hlarge (b₀ + 1)
    refine ⟨x - b₀, by omega, Submodule.subset_span ⟨x - b₀, ?_, rfl⟩⟩
    show b₀ + (x - b₀) ∈ M
    rwa [show b₀ + (x - b₀) = x by omega]
  set d := Nat.find hex with hddef
  have hd : 0 < d ∧ (d : ℤ) ∈ I := Nat.find_spec hex
  -- `d` divides every element of `D`
  have hdvd : ∀ u ∈ D, d ∣ u := by
    intro u hu
    have hu' : (u : ℤ) ∈ I := Submodule.subset_span ⟨u, hu, rfl⟩
    have hmod : ((u % d : ℕ) : ℤ) ∈ I := by
      have e : ((u % d : ℕ) : ℤ) = (u : ℤ) - ((u / d : ℕ) : ℤ) * (d : ℤ) := by
        have := Nat.mod_add_div u d
        push_cast
        linarith [this]
      rw [e]
      exact I.sub_mem hu' (I.smul_mem _ hd.2)
    by_contra hnd
    have hpos : 0 < u % d := Nat.pos_of_ne_zero fun h ↦ hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt u hd.1) ⟨hpos, hmod⟩
  have hdecomp : ∀ x ∈ M, b₀ ≤ x → ∃ q, x = b₀ + d * q ∧ q ∈ {y | b₀ + d * y ∈ M} := by
    intro x hx hxb
    have hu : x - b₀ ∈ D := by
      show b₀ + (x - b₀) ∈ M
      rwa [show b₀ + (x - b₀) = x by omega]
    obtain ⟨q, hq⟩ := hdvd _ hu
    refine ⟨q, by omega, ?_⟩
    show b₀ + d * q ∈ M
    rwa [← hq, show b₀ + (x - b₀) = x by omega]
  set E : Set ℕ := {y | b₀ + d * y ∈ M} with hE
  have hE0 : 0 ∈ E := by simpa [hE] using hb₀
  -- a finite generating subset of `E`
  obtain ⟨T, hTD, hdT⟩ := Submodule.mem_span_finite_of_mem_span hd.2
  set F : Finset ℕ := T.image fun z ↦ z.toNat / d with hF
  have hFE : (F : Set ℕ) ⊆ E := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    obtain ⟨u, hu, rfl⟩ := hTD hz
    show b₀ + d * ((u : ℤ).toNat / d) ∈ M
    rw [Int.toNat_natCast, Nat.mul_div_cancel' (hdvd u hu)]
    exact hu
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F) := by
    set f : ℤ →ₗ[ℤ] ℤ := LinearMap.mulLeft ℤ (d : ℤ) with hf
    have hT : (T : Set ℤ) ⊆ f '' ((Nat.cast : ℕ → ℤ) '' F) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hTD hz
      refine ⟨((u / d : ℕ) : ℤ), ⟨u / d, mem_image.2 ⟨u, hz, by simp⟩, rfl⟩, ?_⟩
      simp only [hf, LinearMap.mulLeft_apply]
      exact_mod_cast Nat.mul_div_cancel' (hdvd u hu)
    have hmem : (d : ℤ) ∈ Submodule.map f (Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono hT hdT
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.1 hmem
    have hy1 : y = 1 := by
      simp only [hf, LinearMap.mulLeft_apply] at hfy
      have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.1.ne'
      exact mul_left_cancel₀ hd0 (hfy.trans (mul_one _).symm)
    rwa [hy1] at hy
  -- counting `M` through `E`
  have hcntM : ∀ b, cnt M b ≤ b₀ + cnt E b := by
    intro b
    unfold cnt
    have hsub : (range b).filter (· ∈ M) ⊆
        range b₀ ∪ ((range b).filter (· ∈ E)).image fun y ↦ b₀ + d * y := by
      intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_union, mem_range, mem_image]
      by_cases hxb : x < b₀
      · exact Or.inl hxb
      · obtain ⟨q, rfl, hq⟩ := hdecomp x hx.2 (by omega)
        have : q ≤ d * q := Nat.le_mul_of_pos_left q hd.1
        exact Or.inr ⟨q, mem_filter.2 ⟨mem_range.2 (by omega), hq⟩, rfl⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := by rw [card_range]; exact Nat.add_le_add_left card_image_le _
  have hcntM2 : ∀ b, cnt M b ≤ b₀ + (b / d + 1) := by
    intro b
    unfold cnt
    have hsub : (range b).filter (· ∈ M) ⊆
        range b₀ ∪ (range (b / d + 1)).image fun y ↦ b₀ + d * y := by
      intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_union, mem_range, mem_image]
      by_cases hxb : x < b₀
      · exact Or.inl hxb
      · obtain ⟨q, rfl, -⟩ := hdecomp x hx.2 (by omega)
        refine Or.inr ⟨q, mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
        rw [Nat.le_div_iff_mul_le hd.1, mul_comm]
        omega
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add (card_range _).le (card_image_le.trans (card_range _).le)
  -- `d ≤ K`
  have hdK : d ≤ K := by
    by_contra hdK
    push Not at hdK
    set b := N + ⌈(2 * (b₀ : ℝ) + 2) / γ⌉₊ with hb
    have h1 := hN b (by omega)
    have h2 := hcntM2 b
    set q := b / d with hq
    have h3 : q * d ≤ b := Nat.div_mul_le_self b d
    have h4 : q * K ≤ b := (Nat.mul_le_mul_left q hdK.le).trans h3
    have h5 : ((2 * (b₀ : ℝ) + 2) / γ) ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(2 * (b₀ : ℝ) + 2) / γ⌉₊ ≤ b))
    have h6 : 2 * (b₀ : ℝ) + 2 ≤ γ * b := by rw [div_le_iff₀ hγ] at h5; linarith
    have h2' : (cnt M b : ℝ) ≤ b₀ + (q + 1) := by exact_mod_cast h2
    have h4' : (q : ℝ) * K ≤ b := by exact_mod_cast h4
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have h7 : 4 * (q : ℝ) ≤ γ * b := by
      have := mul_le_mul_of_nonneg_left h4' hγ.le
      nlinarith
    linarith
  -- density of `E`
  have hdens : ∃ N₁, ∀ b ≥ N₁, γ / 2 * b ≤ cnt E b := by
    refine ⟨N + ⌈2 * (b₀ : ℝ) / γ⌉₊, fun b hb ↦ ?_⟩
    have h1 := hN b (by omega)
    have h2 : (cnt M b : ℝ) ≤ b₀ + cnt E b := by exact_mod_cast hcntM b
    have h3 : 2 * (b₀ : ℝ) / γ ≤ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 * (b₀ : ℝ) / γ⌉₊ ≤ b))
    have h4 : 2 * (b₀ : ℝ) ≤ γ * b := by rw [div_le_iff₀ hγ] at h3; linarith
    linarith
  obtain ⟨N', hN'⟩ := hcov E hE0 ⟨F, hFE, h1⟩ hdens
  refine ⟨d, b₀, N', hd.1, hdK, fun x hx ↦ ?_⟩
  obtain ⟨Me, hMe1, hMe2, hMe3⟩ := hN' x hx
  refine ⟨Me.map fun y ↦ b₀ + d * y, by simp [hMe1], ?_, ?_⟩
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 ha
    exact hMe2 y hy
  · rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, Multiset.sum_map_mul_left,
      Multiset.map_id', hMe3, hMe1, smul_eq_mul]
end Erdos338Proof
