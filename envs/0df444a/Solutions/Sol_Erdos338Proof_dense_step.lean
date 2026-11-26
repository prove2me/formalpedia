-- Prove2me | solution 1 for Erdos338Proof.dense_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:43.560045+00:00
-- url     : https://prove2.me/submissions/bc1c6c15-9cd3-4dfb-a0da-f6ad974dd755

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure
public import Theorems.Thm_Erdos338Proof_exists_multiset_of_nsmul_eq_univ
public import Theorems.Thm_Erdos338Proof_nsmul_eq_univ


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {γ : ℝ} (hγ : 0 < γ) {h : ℕ} (hh : (4 / γ : ℝ) < h) {E : Set ℕ}
    {F : Finset ℕ} (hFE : (F : Set ℕ) ⊆ E)
    (h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) (hE0 : 0 ∈ E) {ℓ : ℕ} (hℓE : ℓ ∈ E)
    (hℓN : N ≤ ℓ) (hℓF : F.sup id ≤ ℓ) (hℓγ : (2 / γ : ℝ) ≤ ℓ) {m x : ℕ}
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  classical
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < 2 / γ := by positivity
    exact_mod_cast this.trans_le hℓγ
  have : NeZero ℓ := ⟨hℓpos.ne'⟩
  set A := (range (ℓ + 1)).filter (· ∈ E) with hA
  have hA0 : 0 ∈ A := by simp [hA, hE0]
  have hAℓ : ℓ ∈ A := by simp [hA, hℓE]
  have hle : ∀ a ∈ A, a ≤ ℓ := by
    intro a ha
    simp only [hA, mem_filter, mem_range] at ha
    omega
  set f := Nat.castAddMonoidHom (ZMod ℓ)
  set S := A.image f with hS
  -- `S` is large
  have hAcnt : γ * ℓ ≤ #A := by
    have h1 := hN ℓ hℓN
    have h2 : cnt E ℓ ≤ #A := by
      unfold cnt
      apply card_le_card
      intro a ha
      simp only [mem_filter, mem_range] at ha
      rw [hA]
      exact mem_filter.2 ⟨mem_range.2 (by omega), ha.2⟩
    exact h1.trans (by exact_mod_cast h2)
  have hScard : #A ≤ #S + 1 := by
    have hinj : Set.InjOn f (A.erase ℓ : Set ℕ) := by
      intro a ha b hb hab
      simp only [coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
      have ha' : a < ℓ := lt_of_le_of_ne (hle a ha.1) ha.2
      have hb' : b < ℓ := lt_of_le_of_ne (hle b hb.1) hb.2
      have := congrArg ZMod.val hab
      simp only [f, Nat.coe_castAddMonoidHom, ZMod.val_natCast] at this
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    have h1 : #(A.erase ℓ) ≤ #S := by
      rw [← card_image_of_injOn hinj]
      exact card_le_card (image_subset_image (erase_subset ℓ A))
    have h2 := card_erase_add_one hAℓ
    omega
  have hcard : 2 * Fintype.card (ZMod ℓ) ≤ h * #S := by
    rw [ZMod.card]
    have hS' : (γ * ℓ - 1 : ℝ) ≤ #S := by
      have : (#A : ℝ) ≤ #S + 1 := by exact_mod_cast hScard
      linarith
    have hpos : (0 : ℝ) ≤ γ * ℓ - 1 := by
      have : γ * (2 / γ) ≤ γ * ℓ := mul_le_mul_of_nonneg_left hℓγ hγ.le
      rw [mul_div_cancel₀ _ hγ.ne'] at this
      linarith
    have key : (4 / γ) * (γ * ℓ - 1) ≤ (h : ℝ) * #S :=
      mul_le_mul hh.le hS' hpos (by positivity)
    have e : (4 / γ) * (γ * ℓ - 1) = 4 * ℓ - 4 / γ := by field_simp
    have h4 : (4 / γ : ℝ) ≤ 2 * ℓ := by
      have : (4 / γ : ℝ) = 2 * (2 / γ) := by ring
      linarith
    have : (2 * ℓ : ℝ) ≤ h * #S := by linarith
    exact_mod_cast this
  -- `S` generates `ZMod ℓ`
  have hgen : AddSubgroup.closure (S : Set (ZMod ℓ)) = ⊤ := by
    set φ : ℤ →ₗ[ℤ] ZMod ℓ := (Int.castAddHom (ZMod ℓ)).toIntLinearMap
    have hmap : (1 : ZMod ℓ) ∈ Submodule.span ℤ (S : Set (ZMod ℓ)) := by
      have h2 : φ 1 ∈ Submodule.span ℤ (φ '' ((Nat.cast : ℕ → ℤ) '' F)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have e1 : φ 1 = 1 := by simp [φ]
      rw [e1] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, ?_, by simp [φ, f]⟩)
      simp only [hA, mem_filter, mem_range]
      refine ⟨?_, hFE hn⟩
      have : n ≤ F.sup id := Finset.le_sup (f := id) hn
      omega
    replace hmap : (1 : ZMod ℓ) ∈ (Submodule.span ℤ (S : Set (ZMod ℓ))).toAddSubgroup := hmap
    rw [Submodule.span_int_eq_addSubgroupClosure] at hmap
    rw [eq_top_iff]
    intro z _
    have : (z.val : ℕ) • (1 : ZMod ℓ) ∈ AddSubgroup.closure (S : Set (ZMod ℓ)) :=
      AddSubgroup.nsmul_mem _ hmap _
    simpa using this
  have h0S : (0 : ZMod ℓ) ∈ S := Finset.mem_image.2 ⟨0, hA0, by simp [f]⟩
  have hh1 : 1 ≤ h := by
    have : (0 : ℝ) < h := lt_of_le_of_lt (by positivity) hh
    exact_mod_cast this
  have huniv := nsmul_eq_univ h0S hgen hh1 hcard
  obtain ⟨M, hMc, hMA, hMs⟩ := exists_multiset_of_nsmul_eq_univ hA0 hAℓ hle huniv hx1 hx2
  refine ⟨M, hMc, fun a ha ↦ ?_, hMs⟩
  have := hMA a ha
  simp only [hA, mem_filter] at this
  exact this.2
end Erdos338Proof
