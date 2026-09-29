-- Prove2me | solution 1 for CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b0c8db20-c6e1-5de5-b9d3-7cdee4f649a6

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq
import Theorems.Thm_PeriodPair_weierstrassP_scale
import Theorems.Thm_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero
import Theorems.Thm_Polynomial_eq_of_forall_sum_roots_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ComplexConjugate
open PeriodPair Complex

namespace CohCarrier
p2m_export "CohCarrier" "gamma0Units GammaH mem_GammaH_iff"
namespace DivisionValuesCore
p2m_open "CohCarrier"

theorem multiset_eq_of_forall_sum_pow_eq (s t : Multiset ℂ) (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ n : ℕ, 0 < n → (s.map (· ^ n)).sum = (t.map (· ^ n)).sum) : s = t := by
  have hsplit : ∀ u : Multiset ℂ, (u.map fun a => Polynomial.X - Polynomial.C a).prod.Splits :=
    fun u => Polynomial.Splits.multisetProd (by
      intro f hf
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hf
      exact Polynomial.Splits.X_sub_C a)
  have hmonic : ∀ u : Multiset ℂ, (u.map fun a => Polynomial.X - Polynomial.C a).prod.Monic :=
    fun u => Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have key := Polynomial.eq_of_forall_sum_roots_pow_eq
    ((s.map fun a => Polynomial.X - Polynomial.C a).prod)
    ((t.map fun a => Polynomial.X - Polynomial.C a).prod)
    (hmonic s) (hmonic t) (hsplit s) (hsplit t)
    (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard])
    (by
      intro n hn
      rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C]
      exact h n hn)
  have := congrArg Polynomial.roots key
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

lemma int_indep (τ : UpperHalfPlane) {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = m' * τ + n') : m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im,
    UpperHalfPlane.coe_re] at him
  have hm : m = m' := by
    have : ((m : ℝ) - m') * τ.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact_mod_cast sub_eq_zero.1 h0
    · exact absurd h0 τ.im_pos.ne'
  subst hm
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

lemma mem_ofTau_lattice (τ : UpperHalfPlane) (x : ℂ) :
    x ∈ (ofTau τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) * τ + n = x := by
  rw [PeriodPair.mem_lattice]
  simp only [ofTau_ω₁, ofTau_ω₂, mul_one]

lemma mem_scale_lattice (L : PeriodPair) (α : ℂˣ) (x : ℂ) :
    x ∈ (L.scale α).lattice ↔ ∃ m n : ℤ, (α : ℂ) * (m * L.ω₁ + n * L.ω₂) = x := by
  rw [PeriodPair.mem_lattice]
  simp only [scale_ω₁, scale_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩

lemma weierstrassP_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (z : ℂ) :
    L.weierstrassP z = L'.weierstrassP z := by
  unfold PeriodPair.weierstrassP
  rw [h]

lemma div_notMem (N : ℕ) [NeZero N] (hN : N ≠ 1) (τ : UpperHalfPlane) (u : (ZMod N)ˣ) :
    (((u : ZMod N).val : ℂ) / N) ∉ (ofTau τ).lattice := by
  haveI : Fact (1 < N) := ⟨lt_of_le_of_ne (NeZero.one_le) (Ne.symm hN)⟩
  intro hmem
  obtain ⟨m, n, hmn⟩ := (mem_ofTau_lattice τ _).1 hmem
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h := int_indep τ (m := m) (n := n) (m' := 0) (n' := 0)

  have him := congrArg Complex.im hmn
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im,
    UpperHalfPlane.coe_re, div_natCast_im, natCast_im, zero_div] at him
  have hm : m = 0 := by
    rcases mul_eq_zero.1 him with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 τ.im_pos.ne'
  subst hm
  simp only [Int.cast_zero, zero_mul, zero_add] at hmn

  have hval : (n : ℂ) * N = ((u : ZMod N).val : ℂ) := by
    rw [hmn, div_mul_cancel₀ _ hN0]
  have hval' : n * (N : ℤ) = ((u : ZMod N).val : ℤ) := by exact_mod_cast hval
  have hdvd : (N : ℤ) ∣ ((u : ZMod N).val : ℤ) := ⟨n, by rw [← hval']; ring⟩
  have hdvd' : N ∣ (u : ZMod N).val := Int.natCast_dvd_natCast.1 hdvd
  have hlt : (u : ZMod N).val < N := ZMod.val_lt _
  have hpos : 0 < (u : ZMod N).val := by
    rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
    exact Units.ne_zero u
  exact absurd (Nat.le_of_dvd hpos hdvd') (not_le.2 hlt)

theorem finish (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (τ : UpperHalfPlane)
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (h₀ : (ZMod N)ˣ) (hh₀ : h₀ ∈ H)
    (ι : ℂ) (hιn : ι * conj ι = 1) (hι1 : ι ∈ (ofTau τ).lattice) (hιτ : ι * τ ∈ (ofTau τ).lattice)
    (hrel : ((((CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ : (ZMod N)ˣ) : ZMod N).val : ℂ) -
        ι * ((h₀ : ZMod N).val : ℂ)) / N ∈ (ofTau τ).lattice) :
    ∃ γ ∈ CohCarrier.GammaH N H, γ • τ = γ₀ • τ := by
  set d₀ : (ZMod N)ˣ := CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ with hd₀
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  obtain ⟨e, f, hef⟩ := (mem_ofTau_lattice τ _).1 hι1
  obtain ⟨e', f', hef'⟩ := (mem_ofTau_lattice τ _).1 hιτ
  obtain ⟨m, n, hmn⟩ := (mem_ofTau_lattice τ _).1 hrel

  have hlin : ((N * m + e * (h₀ : ZMod N).val : ℤ) : ℂ) * τ + ((N * n + f * (h₀ : ZMod N).val : ℤ) : ℂ)
      = ((0 : ℤ) : ℂ) * τ + (((d₀ : ZMod N).val : ℤ) : ℂ) := by
    have h1 : ((m : ℂ) * τ + n) * N = ((d₀ : ZMod N).val : ℂ) - ι * ((h₀ : ZMod N).val : ℂ) := by
      rw [hmn, div_mul_cancel₀ _ hN0]
    rw [← hef] at h1
    push_cast
    linear_combination h1
  obtain ⟨hc1, hc2⟩ := int_indep τ hlin
  have hz1 : ((e : ZMod N)) * (h₀ : ZMod N) = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hc1
    push_cast at this
    simpa [ZMod.natCast_self, ZMod.natCast_zmod_val] using this
  have he : (e : ZMod N) = 0 := (Units.mul_left_eq_zero h₀).1 hz1
  have hz2 : ((f : ZMod N)) * (h₀ : ZMod N) = (d₀ : ZMod N) := by
    have := congrArg (Int.cast : ℤ → ZMod N) hc2
    push_cast at this
    simpa [ZMod.natCast_self, ZMod.natCast_zmod_val] using this

  have hι0 : ι ≠ 0 := by
    rintro rfl; simp at hιn
  set τc : ℂ := conj (τ : ℂ) with hτc
  have hconj1 : conj ι = e * τc + f := by
    rw [← hef]; simp [hτc]
  have hconj2 : conj ι * τc = e' * τc + f' := by
    have := congrArg conj hef'
    simp only [map_add, map_mul, map_intCast] at this
    rw [← this, hτc]
  have hdetC : ((e' * f - f' * e : ℤ) : ℂ) * ((τ : ℂ) - τc) = (τ : ℂ) - τc := by
    push_cast
    linear_combination (-((e' : ℂ) * τc + f')) * hef + conj ι * hef' +
      (-((e' : ℂ) * τ + f')) * hconj1 + ι * hconj2 + ((τ : ℂ) - τc) * hιn
  have hττc : (τ : ℂ) - τc ≠ 0 := by
    rw [hτc, Complex.sub_conj]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero two_ne_zero (UpperHalfPlane.im_ne_zero τ)
  have hdet : e' * f - f' * e = 1 := by
    have : ((e' * f - f' * e : ℤ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hττc (hdetC.trans (one_mul _).symm)
      exact this
    exact_mod_cast this

  let ε : SL(2, ℤ) := ⟨!![e', f'; e, f], by rw [Matrix.det_fin_two_of]; linarith⟩
  have hεΓ : ε ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simpa [ε] using he
  have hετ : ε • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [ε, algebraMap_int_eq, eq_intCast, ofReal_intCast, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    rw [hef, hef', div_eq_iff hι0, mul_comm]

  refine ⟨γ₀ * ε⁻¹, ?_, ?_⟩
  · rw [CohCarrier.mem_GammaH_iff]
    refine ⟨Subgroup.mul_mem _ hγ₀ (Subgroup.inv_mem _ hεΓ), ?_⟩
    have hunits : CohCarrier.gamma0Units N ⟨γ₀ * ε⁻¹, Subgroup.mul_mem _ hγ₀ (Subgroup.inv_mem _ hεΓ)⟩
        = d₀ * (CohCarrier.gamma0Units N ⟨ε, hεΓ⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [hunits]
    have hfu : ((CohCarrier.gamma0Units N ⟨ε, hεΓ⟩ : (ZMod N)ˣ) : ZMod N) = (f : ZMod N) := by
      show ((ε 1 1 : ℤ) : ZMod N) = (f : ZMod N)
      simp [ε]
    have heq : d₀ * (CohCarrier.gamma0Units N ⟨ε, hεΓ⟩)⁻¹ = h₀ := by
      rw [mul_inv_eq_iff_eq_mul]
      ext
      rw [Units.val_mul, hfu, ← hz2, mul_comm]
    rw [heq]
    exact hh₀
  · rw [mul_smul, inv_smul_eq_iff.2 hετ.symm]

def rho : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma rho_prim : IsPrimitiveRoot rho 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [rho] using this

lemma rho_cube : rho ^ 3 = 1 := rho_prim.pow_eq_one

lemma rho_six : rho ^ 6 = 1 := by
  rw [show 6 = 3 * 2 from rfl, pow_mul, rho_cube, one_pow]

lemma rho_sq_add : rho ^ 2 + rho + 1 = 0 := by
  have hne : rho ≠ 1 := rho_prim.ne_one (by norm_num)
  have h : (rho - 1) * (rho ^ 2 + rho + 1) = 0 := by
    have := rho_cube; linear_combination this
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

lemma mul_conj_eq_one_of_norm {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

lemma rho_conj : rho * conj rho = 1 :=
  mul_conj_eq_one_of_norm (rho_prim.norm'_eq_one (by norm_num))

lemma rho_ne_zero : rho ≠ 0 := by
  intro h; have := rho_cube; rw [h] at this; norm_num at this

theorem exists_unit (L : PeriodPair) (d : ℕ)
    (hd : d = 1 ∨ (d = 2 ∧ L.g₃ = 0) ∨ (d = 3 ∧ L.g₂ = 0)) {x y : ℂ} (hxy : x ^ d = y ^ d) :
    ∃ (ι : ℂ) (hι : ι ≠ 0), ι * conj ι = 1 ∧ (L.scale (Units.mk0 ι hι)).lattice = L.lattice ∧
      x = (ι ^ 2)⁻¹ * y := by

  have one_case : x = y → ∃ (ι : ℂ) (hι : ι ≠ 0), ι * conj ι = 1 ∧
      (L.scale (Units.mk0 ι hι)).lattice = L.lattice ∧ x = (ι ^ 2)⁻¹ * y := by
    intro h
    refine ⟨1, one_ne_zero, by simp, ?_, by simp [h]⟩
    exact PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero L _
      (Or.inl (by simp)) (Or.inl (by simp))
  rcases hd with rfl | ⟨rfl, hg3⟩ | ⟨rfl, hg2⟩
  · exact one_case (by simpa using hxy)
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hxy with h | h
    · exact one_case h
    · refine ⟨Complex.I, Complex.I_ne_zero, by simp [Complex.conj_I], ?_, ?_⟩
      · exact PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero L _
          (Or.inl (by simp [Complex.I_pow_four])) (Or.inr hg3)
      · rw [h, Complex.I_sq]; ring
  · have hfac : (x - y) * (x - rho * y) * (x - rho ^ 2 * y) = 0 := by
      have h3 := rho_cube
      have hs := rho_sq_add
      have : (x - y) * (x - rho * y) * (x - rho ^ 2 * y) = x ^ 3 - y ^ 3 := by
        linear_combination (-x ^ 2 * y + x * y ^ 2) * hs + (x * y ^ 2 - y ^ 3) * h3
      rw [this, hxy, sub_self]
    rcases mul_eq_zero.1 hfac with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact one_case (sub_eq_zero.1 h)
      ·
        refine ⟨rho, rho_ne_zero, rho_conj, ?_, ?_⟩
        · exact PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero L _
            (Or.inr hg2) (Or.inl (by simp [rho_six]))
        · have hinv : (rho ^ 2)⁻¹ = rho :=
            inv_eq_of_mul_eq_one_right (by rw [← pow_succ, rho_cube])
          rw [hinv]; exact sub_eq_zero.1 h
    ·
      refine ⟨rho ^ 2, pow_ne_zero _ rho_ne_zero, ?_, ?_, ?_⟩
      · rw [map_pow, ← mul_pow, rho_conj, one_pow]
      · exact PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero L _
          (Or.inr hg2) (Or.inl (by
            simp only [Units.val_mk0]
            calc (rho ^ 2) ^ 6 = (rho ^ 6) ^ 2 := by ring
              _ = 1 := by rw [rho_six, one_pow]))
      · have hinv : ((rho ^ 2) ^ 2)⁻¹ = rho ^ 2 :=
          inv_eq_of_mul_eq_one_right (by
            calc (rho ^ 2) ^ 2 * rho ^ 2 = rho ^ 6 := by ring
              _ = 1 := rho_six)
        rw [hinv]; exact sub_eq_zero.1 h

end CohCarrier.DivisionValuesCore

open CohCarrier.DivisionValuesCore in
theorem solution (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) [Fintype H] (τ : UpperHalfPlane)
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (d : ℕ)
    (hd : d = 1 ∨ (d = 2 ∧ (PeriodPair.ofTau τ).g₃ = 0) ∨ (d = 3 ∧ (PeriodPair.ofTau τ).g₂ = 0))
    (hsum : ∀ j : ℕ, 0 < j →
      ∑ h : H, (PeriodPair.ofTau τ).weierstrassP ((((h : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ (d * j) =
        ∑ h : H, (PeriodPair.ofTau τ).weierstrassP
          ((((CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ * (h : (ZMod N)ˣ) : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^
            (d * j)) :
    ∃ γ ∈ CohCarrier.GammaH N H, γ • τ = γ₀ • τ := by
  classical

  by_cases hN : N = 1
  · subst hN
    refine ⟨γ₀, ?_, rfl⟩
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hγ₀, ?_⟩
    rw [Subsingleton.elim (CohCarrier.gamma0Units 1 ⟨γ₀, hγ₀⟩) 1]
    exact H.one_mem
  set L : PeriodPair := PeriodPair.ofTau τ with hL
  set d₀ : (ZMod N)ˣ := CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ with hd₀

  set φ : (ZMod N)ˣ → ℂ := fun u => L.weierstrassP (((u : ZMod N).val : ℂ) / N) with hφ

  have hms : (Finset.univ : Finset H).val.map (fun h : H => φ (h : (ZMod N)ˣ) ^ d) =
      (Finset.univ : Finset H).val.map (fun h : H => φ (d₀ * (h : (ZMod N)ˣ)) ^ d) := by
    apply multiset_eq_of_forall_sum_pow_eq
    · simp
    · intro n hn
      simp only [Multiset.map_map, Function.comp_def, ← pow_mul]
      rw [← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum]
      simp only [hφ]
      exact hsum n hn
  have hmem : φ d₀ ^ d ∈ (Finset.univ : Finset H).val.map (fun h : H => φ (h : (ZMod N)ˣ) ^ d) := by
    rw [hms, Multiset.mem_map]
    exact ⟨1, Finset.mem_univ _, by simp⟩
  obtain ⟨h₀, -, hh₀⟩ := Multiset.mem_map.1 hmem

  obtain ⟨ι, hι0, hιn, hιΛ, hιv⟩ := exists_unit L d hd hh₀.symm

  have hscale : L.weierstrassP (ι * ((((h₀ : (ZMod N)ˣ) : ZMod N).val : ℂ) / N)) = (ι ^ 2)⁻¹ * φ h₀ := by
    have := PeriodPair.weierstrassP_scale L (Units.mk0 ι hι0) ((((h₀ : (ZMod N)ˣ) : ZMod N).val : ℂ) / N)
    rw [weierstrassP_congr hιΛ] at this
    simpa only [Units.val_mk0, hφ] using this
  have heqP : L.weierstrassP ((((d₀ : ZMod N)).val : ℂ) / N) =
      L.weierstrassP (ι * ((((h₀ : (ZMod N)ˣ) : ZMod N).val : ℂ) / N)) := by
    rw [hscale]
    simpa only [hφ] using hιv
  have ha : ((((d₀ : ZMod N)).val : ℂ) / N) ∉ L.lattice := div_notMem N hN τ d₀
  have hb : ι * ((((h₀ : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ∉ L.lattice := by
    intro hb
    apply div_notMem N hN τ (h₀ : (ZMod N)ˣ)
    rw [← hιΛ] at hb
    obtain ⟨m, n, hmn⟩ := (mem_scale_lattice L _ _).1 hb
    simp only [Units.val_mk0] at hmn
    have := mul_left_cancel₀ hι0 hmn
    rw [PeriodPair.mem_lattice]
    exact ⟨m, n, this⟩
  have hι1 : ι ∈ L.lattice := by
    have := (L.scale (Units.mk0 ι hι0)).ω₂_mem_lattice
    rw [hιΛ] at this
    simpa [hL] using this
  have hιτ : ι * τ ∈ L.lattice := by
    have := (L.scale (Units.mk0 ι hι0)).ω₁_mem_lattice
    rw [hιΛ] at this
    simpa [hL] using this

  rcases PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq L ha hb heqP with h | h
  · refine finish N H τ γ₀ hγ₀ (h₀ : (ZMod N)ˣ) h₀.2 ι hιn hι1 hιτ ?_
    convert h using 1
    ring
  · refine finish N H τ γ₀ hγ₀ (h₀ : (ZMod N)ˣ) h₀.2 (-ι) (by simpa using hιn) (neg_mem hι1) ?_ ?_
    · have h__af := neg_mem hιτ
      simp at h__af ⊢
      exact h__af
    · convert h using 1
      ring

end
end S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq
end P2MW
export P2MW.S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq (solution)
