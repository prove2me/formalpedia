-- Prove2me | solution 1 for DualCoppersmith.Recovery.first_vector_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:30:06.63235+00:00
-- url     : https://prove2.me/submissions/dff1ac1e-18e3-4629-86a3-e15cd8fbedb3

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting
import Definitions.Def_RegevLWE_SmoothingLB_Lattice
import Definitions.Def_DualCoppersmith_Recovery_Geometry

section
set_option autoImplicit false

namespace DualCoppersmith.Dev.FirstVector

open LLLFactor.RedBasis

lemma inner_b_gs {n : ℕ} (b : Fin n → Vec n) (i k : Fin n) (h : i ≤ k) :
    inner ℝ (b i) (gs b k) = if i = k then ‖gs b k‖ ^ 2 else 0 := by
  have h1 := InnerProductSpace.gramSchmidt_def'' ℝ b i
  have h2 : inner ℝ (b i) (gs b k) = inner ℝ (gs b i) (gs b k) +
      ∑ j ∈ Finset.Iio i, (inner ℝ (InnerProductSpace.gramSchmidt ℝ b j) (b i)
        / ‖InnerProductSpace.gramSchmidt ℝ b j‖ ^ 2) *
        inner ℝ (InnerProductSpace.gramSchmidt ℝ b j) (gs b k) := by
    conv_lhs => rw [h1]
    rw [inner_add_left, sum_inner]
    simp only [inner_smul_left, gs]
    simp
  rw [h2]
  have hs : ∑ j ∈ Finset.Iio i, (inner ℝ (InnerProductSpace.gramSchmidt ℝ b j) (b i)
        / ‖InnerProductSpace.gramSchmidt ℝ b j‖ ^ 2) *
        inner ℝ (InnerProductSpace.gramSchmidt ℝ b j) (gs b k) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have : j ≠ k := by
      have := Finset.mem_Iio.mp hj
      exact ne_of_lt (lt_of_lt_of_le this h)
    rw [show inner ℝ (InnerProductSpace.gramSchmidt ℝ b j) (gs b k) = 0 from
      InnerProductSpace.gramSchmidt_orthogonal ℝ b this]
    simp
  rw [hs, add_zero]
  by_cases hik : i = k
  · subst hik
    simp [gs, real_inner_self_eq_norm_sq]
  · simp only [hik, if_false]
    exact InnerProductSpace.gramSchmidt_orthogonal ℝ b hik

lemma exists_gs_le {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
    (x : Vec n) (hx : x ∈ latticeOf b) (hx0 : x ≠ 0) :
    ∃ k, ‖gs b k‖ ≤ ‖x‖ := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have hne : (Finset.univ.filter (fun i => c i ≠ 0)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hx0
    rw [← hc]
    apply Finset.sum_eq_zero
    intro i _
    have : ¬ c i ≠ 0 := fun hh => by
      have : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [hh]
      rw [h] at this; simp at this
    rw [not_not] at this
    simp [this]
  set k := (Finset.univ.filter (fun i => c i ≠ 0)).max' hne with hk
  have hkc : c k ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa [← hk] using this
  have hgt : ∀ i, k < i → c i = 0 := by
    intro i hi
    by_contra hci
    have : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [hci]
    have := Finset.le_max' _ i this
    exact absurd hi (not_lt.mpr this)
  have hgsk : gs b k ≠ 0 := InnerProductSpace.gramSchmidt_ne_zero k hb
  have hpos : 0 < ‖gs b k‖ := norm_pos_iff.mpr hgsk
  have hinner : inner ℝ x (gs b k) = (c k : ℝ) * ‖gs b k‖ ^ 2 := by
    rw [← hc, sum_inner]
    rw [Finset.sum_eq_single k]
    · rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, inner_b_gs b k k le_rfl]
      simp
    · intro i _ hik
      rcases lt_or_gt_of_ne hik with h | h
      · rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, inner_b_gs b i k h.le]
        simp [hik]
      · rw [hgt i h]; simp
    · simp
  refine ⟨k, ?_⟩
  have hck : (1 : ℝ) ≤ |(c k : ℝ)| := by
    have : (1 : ℤ) ≤ |c k| := Int.one_le_abs hkc
    exact_mod_cast this
  have hcs := abs_real_inner_le_norm x (gs b k)
  rw [hinner, abs_mul, abs_of_nonneg (sq_nonneg ‖gs b k‖)] at hcs
  have : ‖gs b k‖ ^ 2 ≤ ‖x‖ * ‖gs b k‖ := by
    calc ‖gs b k‖ ^ 2 = 1 * ‖gs b k‖ ^ 2 := by ring
      _ ≤ |(c k : ℝ)| * ‖gs b k‖ ^ 2 := by gcongr
      _ ≤ _ := hcs
  nlinarith

lemma gs_zero_le {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n) (delta : ℝ) (hdelta : 1 ≤ delta)
    (hq : DualCoppersmith.Recovery.GSQuality delta b) (i : ℕ) (hi : i < n) :
    ‖gs b ⟨0, hn⟩‖ ≤ delta ^ (2 * i) * ‖gs b ⟨i, hi⟩‖ := by
  have hd0 : 0 < delta := by linarith
  have key : ∀ i : ℕ, ∀ hi : i < n, ‖gs b ⟨0, hn⟩‖ ^ 2 ≤ delta ^ (4 * i) * ‖gs b ⟨i, hi⟩‖ ^ 2 := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ m ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hq m hi
      calc ‖gs b ⟨0, hn⟩‖ ^ 2 ≤ delta ^ (4 * m) * ‖gs b ⟨m, by omega⟩‖ ^ 2 := h1
        _ ≤ delta ^ (4 * m) * (delta ^ 4 * ‖gs b ⟨m + 1, hi⟩‖ ^ 2) := by gcongr
        _ = delta ^ (4 * (m + 1)) * ‖gs b ⟨m + 1, hi⟩‖ ^ 2 := by ring
  have := key i hi
  have h3 : ‖gs b ⟨0, hn⟩‖ ^ 2 ≤ (delta ^ (2 * i) * ‖gs b ⟨i, hi⟩‖) ^ 2 := by
    calc _ ≤ _ := this
      _ = _ := by ring
  exact le_of_sq_le_sq h3 (by positivity)

lemma main {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
    (output : Fin n → Vec n) (hli : LinearIndependent ℝ output) (hL : latticeOf output = L)
    (delta : ℝ) (hdelta : 1 ≤ delta)
    (hq : ∀ x : Vec n, x ∈ L → x ≠ 0 →
      ‖output ⟨0, hn⟩‖ ≤ delta ^ (2 * (n - 1)) * ‖x‖) :
    ‖output ⟨0, hn⟩‖ ≤ delta ^ (2 * (n - 1)) * RegevLWE.SmoothingLB.lambda1 L := by
  have hM : 0 < delta ^ (2 * (n - 1)) := by positivity
  have hmem : output ⟨0, hn⟩ ∈ L := by
    rw [← hL]; exact Submodule.subset_span ⟨_, rfl⟩
  have hne : output ⟨0, hn⟩ ≠ 0 := hli.ne_zero _
  have : ‖output ⟨0, hn⟩‖ / delta ^ (2 * (n - 1)) ≤ RegevLWE.SmoothingLB.lambda1 L := by
    apply le_csInf
    · exact ⟨_, _, hmem, hne, rfl⟩
    · rintro r ⟨v, hv, hv0, rfl⟩
      rw [div_le_iff₀ hM, mul_comm]
      exact hq v hv hv0
  rwa [div_le_iff₀ hM, mul_comm] at this

end DualCoppersmith.Dev.FirstVector

namespace DualCoppersmith.Recovery

open LLLFactor.RedBasis

theorem chk_first_vector_bound {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
    (input output : Fin n → Vec n) (hinput : IsBasisFor input L)
    (delta : ℝ) (hdelta : 1 ≤ delta) (hcall : IsLLLCall delta input output) :
    ‖output ⟨0, hn⟩‖ ≤ delta ^ (2 * (n - 1)) * RegevLWE.SmoothingLB.lambda1 L := by
  obtain ⟨⟨hli, hlat⟩, _, hq⟩ := hcall
  have hL : latticeOf output = L := by rw [hlat, hinput.2]
  apply DualCoppersmith.Dev.FirstVector.main hn L output hli hL delta hdelta
  intro x hx hx0
  rw [← hL] at hx
  rcases hq with hq | hq
  · obtain ⟨k, hk⟩ := DualCoppersmith.Dev.FirstVector.exists_gs_le output hli x hx hx0
    have h1 := DualCoppersmith.Dev.FirstVector.gs_zero_le hn output delta hdelta hq k k.2
    have h2 : delta ^ (2 * (k : ℕ)) ≤ delta ^ (2 * (n - 1)) :=
      pow_le_pow_right₀ hdelta (by have := k.2; omega)
    have h0 : gs output ⟨0, hn⟩ = output ⟨0, hn⟩ := by
      have h := InnerProductSpace.gramSchmidt_def'' ℝ output ⟨0, hn⟩
      have he : Finset.Iio (⟨0, hn⟩ : Fin n) = ∅ := by
        ext j; simp [Fin.lt_def]
      rw [he] at h
      simpa [gs] using h.symm
    rw [h0] at h1
    calc ‖output ⟨0, hn⟩‖ ≤ delta ^ (2 * (k : ℕ)) * ‖gs output ⟨k, k.2⟩‖ := h1
      _ ≤ delta ^ (2 * (n - 1)) * ‖x‖ := by
        have : (⟨(k : ℕ), k.2⟩ : Fin n) = k := rfl
        rw [this]
        have : 0 ≤ delta ^ (2 * (n - 1)) := by positivity
        calc _ ≤ delta ^ (2 * (n - 1)) * ‖gs output k‖ := by gcongr
          _ ≤ _ := by gcongr
  · exact hq hn x hx hx0

end DualCoppersmith.Recovery

end

theorem solution : type_of% @DualCoppersmith.Recovery.chk_first_vector_bound := @DualCoppersmith.Recovery.chk_first_vector_bound
