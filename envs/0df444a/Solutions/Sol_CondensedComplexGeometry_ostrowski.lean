-- Prove2me | solution 1 for CondensedComplexGeometry.ostrowski
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T19:31:30.998857+00:00
-- url     : https://prove2.me/submissions/5ba4fdd7-1fee-4eba-b8d8-30b362641717

import Mathlib
import Definitions.Def_CondensedComplexGeometry_berkovich

set_option autoImplicit false

universe u

namespace CondensedComplexGeometry

section

open Polynomial Filter Topology

variable {R : Type*} [CommRing R] [Algebra ℂ R] (v : ↥(BerkovichSpectrum R))

lemma oa_mul (x y : R) : (v.1 (x * y) : ℝ) = v.1 x * v.1 y := by
  rw [v.2.1 x y]; rfl

lemma oa_add (x y : R) : (v.1 (x + y) : ℝ) ≤ v.1 x + v.1 y := by
  have := v.2.2.1 x y
  exact_mod_cast this

lemma oa_alg (c : ℂ) : (v.1 (algebraMap ℂ R c) : ℝ) = ‖c‖ := by
  rw [v.2.2.2 c]; rfl

lemma oa_nonneg (x : R) : 0 ≤ (v.1 x : ℝ) := (v.1 x).2

lemma oa_zero : (v.1 0 : ℝ) = 0 := by
  simpa using oa_alg v 0

lemma oa_one : (v.1 1 : ℝ) = 1 := by
  simpa using oa_alg v 1

lemma oa_neg (x : R) : (v.1 (-x) : ℝ) = v.1 x := by
  have h : -x = algebraMap ℂ R (-1) * x := by simp
  rw [h, oa_mul, oa_alg]; simp

lemma oa_sub_le (x y : R) : (v.1 (x - y) : ℝ) ≤ v.1 x + v.1 y := by
  rw [sub_eq_add_neg, ← oa_neg v y]; exact oa_add v _ _

lemma oa_sub_comm (x y : R) : (v.1 (x - y) : ℝ) = v.1 (y - x) := by
  rw [← neg_sub, oa_neg]

lemma oa_abs_sub (x y : R) : |(v.1 x : ℝ) - v.1 y| ≤ v.1 (x - y) := by
  rw [abs_sub_le_iff]
  constructor
  · have := oa_add v (x - y) y
    simp only [sub_add_cancel] at this; linarith
  · have := oa_add v (y - x) x
    simp only [sub_add_cancel] at this; rw [oa_sub_comm] at this; linarith

/-- `v` as a multiplicative map to `ℝ`. -/
noncomputable def oa_monoidHom : R →* ℝ where
  toFun x := (v.1 x : ℝ)
  map_one' := oa_one v
  map_mul' := oa_mul v

lemma oa_pow (x : R) (n : ℕ) : (v.1 (x ^ n) : ℝ) = (v.1 x : ℝ) ^ n :=
  map_pow (oa_monoidHom v) x n

lemma oa_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    (v.1 (∏ i ∈ s, f i) : ℝ) = ∏ i ∈ s, (v.1 (f i) : ℝ) :=
  map_prod (oa_monoidHom v) f s

/-- distance function to the constants -/
noncomputable def oa_phi (x : R) (c : ℂ) : ℝ := v.1 (x - algebraMap ℂ R c)

lemma oa_phi_lip (x : R) (c c' : ℂ) : |oa_phi v x c - oa_phi v x c'| ≤ ‖c - c'‖ := by
  unfold oa_phi
  refine (oa_abs_sub v _ _).trans (le_of_eq ?_)
  rw [← oa_alg v, oa_sub_comm]; congr 1; simp [map_sub]

lemma oa_phi_cont (x : R) : Continuous (oa_phi v x) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun c c' => ?_).continuous
  simpa [Real.dist_eq, dist_eq_norm] using oa_phi_lip v x c c'

lemma oa_phi_ge (x : R) (c : ℂ) : ‖c‖ - v.1 x ≤ oa_phi v x c := by
  have h := oa_sub_le v x (x - algebraMap ℂ R c)
  rw [sub_sub_cancel, oa_alg] at h
  unfold oa_phi; linarith

lemma oa_phi_nonneg (x : R) (c : ℂ) : 0 ≤ oa_phi v x c := oa_nonneg v _

lemma oa_exists_min (x : R) : ∃ c0, ∀ c, oa_phi v x c0 ≤ oa_phi v x c := by
  refine (oa_phi_cont v x).exists_forall_le ?_
  refine tendsto_atTop_mono (fun c => oa_phi_ge v x c) ?_
  exact tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop

lemma oa_key_ineq (x : R) (c0 : ℂ) (hmin : ∀ c, oa_phi v x c0 ≤ oa_phi v x c)
    (ε : ℂ) (n : ℕ) :
    oa_phi v x (c0 + ε) * oa_phi v x c0 ^ n ≤ oa_phi v x c0 ^ (n + 1) + ‖ε‖ ^ (n + 1) := by
  set m := oa_phi v x c0 with hm
  set y := x - algebraMap ℂ R c0 with hy
  have hζ := Complex.isPrimitiveRoot_exp (n + 1) (by omega)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ))
  have hpoly := X_pow_sub_C_eq_prod hζ (Nat.succ_pos n) (rfl : ε ^ (n + 1) = ε ^ (n + 1))
  have hR := congrArg (Polynomial.aeval y) hpoly
  simp only [map_sub, map_pow, aeval_X, aeval_C, map_prod] at hR
  have hfac : ∀ i, y - algebraMap ℂ R (ζ ^ i * ε) = x - algebraMap ℂ R (c0 + ζ ^ i * ε) := by
    intro i; rw [hy, map_add]; ring
  simp only [hfac] at hR
  have hv := congrArg (fun z => (v.1 z : ℝ)) hR
  rw [oa_prod] at hv
  have hle : (v.1 (y ^ (n + 1) - algebraMap ℂ R ε ^ (n + 1)) : ℝ) ≤ m ^ (n + 1) + ‖ε‖ ^ (n + 1) := by
    refine (oa_sub_le v _ _).trans (le_of_eq ?_)
    rw [oa_pow, oa_pow, oa_alg]; rfl
  rw [hv, Finset.prod_range_succ'] at hle
  simp only [pow_zero, one_mul] at hle
  have hge : m ^ n ≤ ∏ i ∈ Finset.range n, (v.1 (x - algebraMap ℂ R (c0 + ζ ^ (i + 1) * ε)) : ℝ) := by
    calc m ^ n = ∏ _i ∈ Finset.range n, m := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => oa_phi_nonneg v x c0) (fun i _ => hmin _)
  have h0 : 0 ≤ oa_phi v x (c0 + ε) := oa_phi_nonneg v x _
  calc oa_phi v x (c0 + ε) * m ^ n ≤ oa_phi v x (c0 + ε) *
        ∏ i ∈ Finset.range n, (v.1 (x - algebraMap ℂ R (c0 + ζ ^ (i + 1) * ε)) : ℝ) :=
        mul_le_mul_of_nonneg_left hge h0
    _ = _ := by rw [mul_comm]; rfl
    _ ≤ _ := hle

lemma oa_key (x : R) (c0 : ℂ) (hmin : ∀ c, oa_phi v x c0 ≤ oa_phi v x c)
    (hm : 0 < oa_phi v x c0) (ε : ℂ) (hε : ‖ε‖ < oa_phi v x c0) :
    oa_phi v x (c0 + ε) ≤ oa_phi v x c0 := by
  set m := oa_phi v x c0 with hmdef
  have hb : ∀ n : ℕ, oa_phi v x (c0 + ε) ≤ m + ‖ε‖ * (‖ε‖ / m) ^ n := by
    intro n
    have hmn : 0 < m ^ n := pow_pos hm n
    refine le_of_mul_le_mul_right ?_ hmn
    refine (oa_key_ineq v x c0 hmin ε n).trans (le_of_eq ?_)
    rw [div_pow]; field_simp; ring
  have ht : Tendsto (fun n : ℕ => m + ‖ε‖ * (‖ε‖ / m) ^ n) atTop (𝓝 (m + ‖ε‖ * 0)) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (norm_nonneg _) hm.le)
      ((div_lt_one hm).mpr hε)
  have := ge_of_tendsto' ht hb
  simpa using this

lemma oa_exists_zero (x : R) : ∃ c : ℂ, (v.1 (x - algebraMap ℂ R c) : ℝ) = 0 := by
  obtain ⟨c0, hc0⟩ := oa_exists_min v x
  by_contra h
  push Not at h
  have hm : 0 < oa_phi v x c0 := lt_of_le_of_ne (oa_phi_nonneg v x c0) (Ne.symm (h c0))
  set Z : Set ℂ := {c | oa_phi v x c ≤ oa_phi v x c0} with hZ
  have hopen : IsOpen Z := by
    rw [Metric.isOpen_iff]
    intro c hc
    have hceq : oa_phi v x c = oa_phi v x c0 := le_antisymm hc (hc0 c)
    refine ⟨oa_phi v x c0, hm, fun d hd => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hd
    have hmin' : ∀ c', oa_phi v x c ≤ oa_phi v x c' := fun c' => hceq ▸ hc0 c'
    have := oa_key v x c hmin' (hceq ▸ hm) (d - c) (hceq ▸ hd)
    rw [add_sub_cancel] at this
    show oa_phi v x d ≤ oa_phi v x c0
    linarith
  have hclosed : IsClosed Z := isClosed_le (oa_phi_cont v x) continuous_const
  have huniv : Z = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨c0, show oa_phi v x c0 ≤ oa_phi v x c0 from le_rfl⟩
  set r : ℝ := (v.1 x : ℝ) + oa_phi v x c0 + 1
  have hr : 0 ≤ r := by have := oa_nonneg v x; linarith
  have hmem : (r : ℂ) ∈ Z := huniv ▸ Set.mem_univ _
  have hge := oa_phi_ge v x (r : ℂ)
  rw [Complex.norm_real, Real.norm_of_nonneg hr] at hge
  have : oa_phi v x (r : ℂ) ≤ oa_phi v x c0 := hmem
  linarith

lemma oa_exists_unique_zero (x : R) : ∃! c : ℂ, (v.1 (x - algebraMap ℂ R c) : ℝ) = 0 := by
  obtain ⟨c, hc⟩ := oa_exists_zero v x
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have h := oa_sub_le v (x - algebraMap ℂ R c) (x - algebraMap ℂ R c')
  rw [sub_sub_sub_cancel_left, ← map_sub, oa_alg, hc, hc'] at h
  have : ‖c' - c‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma oa_eq_of_zero (x : R) (c c' : ℂ) (hc : (v.1 (x - algebraMap ℂ R c) : ℝ) = 0)
    (hc' : (v.1 (x - algebraMap ℂ R c') : ℝ) = 0) : c = c' :=
  (oa_exists_unique_zero v x).unique hc hc'

/-- The character attached to `v`, as a function. -/
noncomputable def oa_fun (x : R) : ℂ := (oa_exists_unique_zero v x).exists.choose

lemma oa_fun_spec (x : R) : (v.1 (x - algebraMap ℂ R (oa_fun v x)) : ℝ) = 0 :=
  (oa_exists_unique_zero v x).exists.choose_spec

lemma oa_fun_eq (x : R) (c : ℂ) (hc : (v.1 (x - algebraMap ℂ R c) : ℝ) = 0) : oa_fun v x = c :=
  oa_eq_of_zero v x _ _ (oa_fun_spec v x) hc

/-- The `ℂ`-algebra character attached to a point of the Berkovich spectrum. -/
noncomputable def oa_char : R →ₐ[ℂ] ℂ where
  toFun := oa_fun v
  map_one' := oa_fun_eq v 1 1 (by simp [oa_zero])
  map_zero' := oa_fun_eq v 0 0 (by simp [oa_zero])
  map_add' x y := by
    refine oa_fun_eq v _ _ (le_antisymm ?_ (oa_nonneg v _))
    have h := oa_add v (x - algebraMap ℂ R (oa_fun v x)) (y - algebraMap ℂ R (oa_fun v y))
    rw [oa_fun_spec, oa_fun_spec] at h
    have e : x + y - algebraMap ℂ R (oa_fun v x + oa_fun v y) =
        x - algebraMap ℂ R (oa_fun v x) + (y - algebraMap ℂ R (oa_fun v y)) := by
      rw [map_add]; ring
    rw [e]; linarith
  map_mul' x y := by
    refine oa_fun_eq v _ _ (le_antisymm ?_ (oa_nonneg v _))
    have e : x * y - algebraMap ℂ R (oa_fun v x * oa_fun v y) =
        (x - algebraMap ℂ R (oa_fun v x)) * y +
          algebraMap ℂ R (oa_fun v x) * (y - algebraMap ℂ R (oa_fun v y)) := by
      rw [map_mul]; ring
    rw [e]
    refine (oa_add v _ _).trans (le_of_eq ?_)
    rw [oa_mul, oa_mul, oa_fun_spec, oa_fun_spec]; ring
  commutes' c := by
    refine oa_fun_eq v _ _ ?_
    simp [oa_zero]

lemma oa_char_apply (x : R) : oa_char v x = oa_fun v x := rfl

lemma oa_char_spec (x : R) : (v.1 (x - algebraMap ℂ R (oa_char v x)) : ℝ) = 0 :=
  oa_fun_spec v x

lemma oa_char_norm (x : R) : (v.1 x : ℝ) = ‖oa_char v x‖ := by
  have h := oa_abs_sub v x (algebraMap ℂ R (oa_char v x))
  rw [oa_char_spec, oa_alg] at h
  linarith [abs_nonneg ((v.1 x : ℝ) - ‖oa_char v x‖), abs_eq_zero.mp (le_antisymm h (abs_nonneg _))]

lemma oa_char_unique (f : R →ₐ[ℂ] ℂ) (hf : ∀ x : R, (v.1 x : ℝ) = ‖f x‖) : f = oa_char v := by
  ext x
  symm
  refine oa_fun_eq v x (f x) ?_
  rw [hf, map_sub, AlgHom.commutes]
  simp

end

section
variable {R : Type u} [CommRing R] [Algebra ℂ R] (v : ↥(BerkovichSpectrum R))

theorem os_mul (x y : R) : (v.1 (x * y) : ℝ) = v.1 x * v.1 y := by
  rw [v.2.1 x y]; rfl

theorem os_add (x y : R) : (v.1 (x + y) : ℝ) ≤ v.1 x + v.1 y := by
  have := v.2.2.1 x y
  exact_mod_cast this

theorem os_alg (c : ℂ) : (v.1 (algebraMap ℂ R c) : ℝ) = ‖c‖ := by
  rw [v.2.2.2 c]; rfl

theorem os_nonneg (x : R) : 0 ≤ (v.1 x : ℝ) := (v.1 x).2

theorem os_neg (x : R) : (v.1 (-x) : ℝ) = v.1 x := by
  have : -x = algebraMap ℂ R (-1) * x := by simp
  rw [this, os_mul, os_alg]; simp

theorem os_le (a b : R) : (v.1 a : ℝ) ≤ v.1 b + v.1 (a - b) := by
  have := os_add v b (a - b)
  rwa [add_sub_cancel] at this

theorem os_abs_sub (a b : R) : |(v.1 a : ℝ) - v.1 b| ≤ v.1 (a - b) := by
  rw [abs_le]
  have h1 := os_le v a b
  have h2 := os_le v b a
  have h3 : (v.1 (b - a) : ℝ) = v.1 (a - b) := by rw [← os_neg, neg_sub]
  constructor <;> linarith

noncomputable def os_f (x : R) : ℂ := (oa_exists_unique_zero v x).exists.choose

theorem os_f_spec (x : R) : (v.1 (x - algebraMap ℂ R (os_f v x)) : ℝ) = 0 :=
  (oa_exists_unique_zero v x).exists.choose_spec

theorem os_f_eq (x : R) (c : ℂ) (h : (v.1 (x - algebraMap ℂ R c) : ℝ) ≤ 0) :
    os_f v x = c :=
  (oa_exists_unique_zero v x).unique (os_f_spec v x) (le_antisymm h (os_nonneg v _))

theorem os_f_alg (c : ℂ) : os_f v (algebraMap ℂ R c) = c :=
  os_f_eq v _ _ (by rw [sub_self, ← map_zero (algebraMap ℂ R), os_alg]; simp)

theorem os_f_add (x y : R) : os_f v (x + y) = os_f v x + os_f v y := by
  apply os_f_eq
  have e : x + y - algebraMap ℂ R (os_f v x + os_f v y) =
      (x - algebraMap ℂ R (os_f v x)) + (y - algebraMap ℂ R (os_f v y)) := by
    rw [map_add]; ring
  rw [e]
  have := os_add v (x - algebraMap ℂ R (os_f v x)) (y - algebraMap ℂ R (os_f v y))
  rw [os_f_spec, os_f_spec] at this
  linarith

theorem os_f_mul (x y : R) : os_f v (x * y) = os_f v x * os_f v y := by
  apply os_f_eq
  have e : x * y - algebraMap ℂ R (os_f v x * os_f v y) =
      (x - algebraMap ℂ R (os_f v x)) * y +
        algebraMap ℂ R (os_f v x) * (y - algebraMap ℂ R (os_f v y)) := by
    rw [map_mul]; ring
  rw [e]
  have := os_add v ((x - algebraMap ℂ R (os_f v x)) * y)
    (algebraMap ℂ R (os_f v x) * (y - algebraMap ℂ R (os_f v y)))
  rw [os_mul, os_mul, os_f_spec, os_f_spec] at this
  linarith

noncomputable def os_char : R →ₐ[ℂ] ℂ where
  toFun := os_f v
  map_one' := by rw [← map_one (algebraMap ℂ R), os_f_alg]
  map_mul' := os_f_mul v
  map_zero' := by rw [← map_zero (algebraMap ℂ R), os_f_alg]
  map_add' := os_f_add v
  commutes' := os_f_alg v

theorem os_char_apply (x : R) : os_char v x = os_f v x := rfl

theorem os_norm (x : R) : (v.1 x : ℝ) = ‖os_f v x‖ := by
  have h := os_abs_sub v x (algebraMap ℂ R (os_f v x))
  rw [os_f_spec, os_alg] at h
  have := abs_nonneg ((v.1 x : ℝ) - ‖os_f v x‖)
  have : |(v.1 x : ℝ) - ‖os_f v x‖| = 0 := le_antisymm h this
  linarith [abs_eq_zero.mp this]

theorem os_continuous_eval (y : R) :
    Continuous (fun w : ↥(BerkovichSpectrum R) => (w.1 y : ℝ)) :=
  NNReal.continuous_coe.comp ((continuous_apply y).comp continuous_subtype_val)

end

theorem os_re_im (z : ℂ) :
    z = (((‖z‖ ^ 2 - ‖z - 1‖ ^ 2 + 1) / 2 : ℝ) : ℂ) +
      (((‖z‖ ^ 2 - ‖z - Complex.I‖ ^ 2 + 1) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
  simp [Complex.sq_norm, Complex.normSq_apply] <;> ring

theorem os_f_formula {R : Type u} [CommRing R] [Algebra ℂ R] (v : ↥(BerkovichSpectrum R))
    (x : R) :
    os_f v x = (((v.1 x : ℝ) ^ 2 - (v.1 (x - algebraMap ℂ R 1) : ℝ) ^ 2 + 1) / 2 : ℝ) +
      ((((v.1 x : ℝ) ^ 2 - (v.1 (x - algebraMap ℂ R Complex.I) : ℝ) ^ 2 + 1) / 2 : ℝ) : ℂ) *
        Complex.I := by
  rw [os_norm v x, os_norm v (x - _), os_norm v (x - _)]
  rw [← os_char_apply, ← os_char_apply, ← os_char_apply, map_sub, map_sub,
    AlgHom.commutes, AlgHom.commutes]
  exact os_re_im _

theorem os_f_continuous {R : Type u} [CommRing R] [Algebra ℂ R] (x : R) :
    Continuous (fun v : ↥(BerkovichSpectrum R) => os_f v x) := by
  simp_rw [os_f_formula]
  have ha := os_continuous_eval (R := R) x
  have hb := os_continuous_eval (R := R) (x - algebraMap ℂ R 1)
  have hc := os_continuous_eval (R := R) (x - algebraMap ℂ R Complex.I)
  fun_prop

theorem os_mem (R : Type u) [CommRing R] [Algebra ℂ R] (f : ↥(ComplexCharacters R)) :
    (fun x => ‖f.1 x‖₊) ∈ BerkovichSpectrum R := by
  obtain ⟨φ, hφ⟩ := f.2
  refine ⟨fun x y => ?_, fun x y => ?_, fun c => ?_⟩
  · simp only [← hφ, map_mul, nnnorm_mul]
  · simp only [← hφ, map_add]; exact nnnorm_add_le _ _
  · simp only [← hφ, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]; rfl

noncomputable def os_g (R : Type u) [CommRing R] [Algebra ℂ R] :
    ↥(ComplexCharacters R) → ↥(BerkovichSpectrum R) :=
  fun f => ⟨fun x => ‖f.1 x‖₊, os_mem R f⟩

theorem os_g_continuous (R : Type u) [CommRing R] [Algebra ℂ R] : Continuous (os_g R) :=
  Continuous.subtype_mk (continuous_pi fun x =>
    continuous_nnnorm.comp ((continuous_apply x).comp continuous_subtype_val)) _

noncomputable def os_e (R : Type u) [CommRing R] [Algebra ℂ R] :
    ↥(BerkovichSpectrum R) ≃ₜ ↥(ComplexCharacters R) where
  toFun v := ⟨os_f v, ⟨os_char v, rfl⟩⟩
  invFun := os_g R
  left_inv v := by
    apply Subtype.ext; funext x
    apply NNReal.eq
    show ‖os_f v x‖ = (v.1 x : ℝ)
    rw [os_norm]
  right_inv f := by
    apply Subtype.ext; funext x
    obtain ⟨φ, hφ⟩ := f.2
    show os_f (os_g R f) x = f.1 x
    apply os_f_eq
    show ‖f.1 (x - algebraMap ℂ R (f.1 x))‖ ≤ 0
    rw [← hφ]; simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self, norm_zero, le_refl]
  continuous_toFun := Continuous.subtype_mk (continuous_pi fun x => os_f_continuous x) _
  continuous_invFun := os_g_continuous R

end CondensedComplexGeometry

open CondensedComplexGeometry in
theorem solution (R : Type u) [CommRing R] [Algebra ℂ R] :
    ∃ (e : ↥(BerkovichSpectrum R) ≃ₜ ↥(ComplexCharacters R)),
      ∀ (v : ↥(BerkovichSpectrum R)) (x : R), (v.1 x : ℝ) = ‖(e v).1 x‖ :=
  ⟨os_e R, fun v x => os_norm v x⟩
