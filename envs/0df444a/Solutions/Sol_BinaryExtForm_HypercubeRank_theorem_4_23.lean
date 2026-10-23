-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.theorem_4_23
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:07:53.57046+00:00
-- url     : https://prove2.me/submissions/e81ed095-5f0c-4409-9af0-22cfd7c1c1f4

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Theorems.Thm_BinaryExtForm_HypercubeRank_corollary_4_19

set_option autoImplicit false

namespace BinaryExtForm.HypercubeRank.LogarithmicProof

noncomputable def blLift {d : ℕ} (y : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (∑ i : Fin d, (2 : ℝ) ^ (i : ℕ) * y i) y

@[simp] lemma blLift_zero {d : ℕ} (y : Fin d → ℝ) :
    blLift y 0 = ∑ i : Fin d, (2 : ℝ) ^ (i : ℕ) * y i := rfl

@[simp] lemma blLift_succ {d : ℕ} (y : Fin d → ℝ) (i : Fin d) :
    blLift y i.succ = y i := rfl

@[simp] lemma yproj_blLift {d : ℕ} (y : Fin d → ℝ) : yproj (blLift y) = y := rfl

noncomputable def blLiftLinear (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun := blLift
  map_add' y z := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp
  map_smul' a y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
    · simp

lemma blLift_injective (d : ℕ) : Function.Injective (@blLift d) := by
  intro y z h
  exact congrArg yproj h

lemma extremePoints_linear_image {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E →ₗ[ℝ] F) (hf : Function.Injective f) (A : Set E) :
    Set.extremePoints ℝ (f '' A) = f '' Set.extremePoints ℝ A := by
  have hmap (u v : E) : f '' openSegment ℝ u v = openSegment ℝ (f u) (f v) := by
    simpa only [LinearMap.coe_toAffineMap] using image_openSegment ℝ f.toAffineMap u v
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx, rfl⟩ := hp.1
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro u hu v hv hseg
    apply hf
    apply hp.2 ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [← hmap]
    exact ⟨x, hseg, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hseg
    rw [← hmap] at hseg
    obtain ⟨w, hw, heq⟩ := hseg
    have hwx : w = x := hf heq
    subst w
    exact congrArg f (hx.2 hu hv hw)

def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Icc 0 1)
def binaryCube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi (fun _ => ({0, 1} : Set ℝ))

lemma mem_binaryCube {d : ℕ} (y : Fin d → ℝ) :
    y ∈ binaryCube d ↔ ∀ i, y i = 0 ∨ y i = 1 := by simp [binaryCube]

lemma BL_eq_lift_cube (d : ℕ) : BL d = blLiftLinear d '' unitCube d := by
  ext p
  constructor
  · intro hp
    refine ⟨yproj p, ?_, ?_⟩
    · intro i _
      exact hp.1 i
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hp.2.symm
      · rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, rfl⟩
    intro i
    exact hy i (Set.mem_univ _)

lemma extremePoints_cube (d : ℕ) : Set.extremePoints ℝ (unitCube d) = binaryCube d := by
  unfold unitCube binaryCube
  rw [extremePoints_pi]
  simp only [Set.extremePoints_Icc (by norm_num : (0 : ℝ) ≤ 1)]

lemma extremePoints_BL (d : ℕ) :
    Set.extremePoints ℝ (BL d) = blLiftLinear d '' binaryCube d := by
  rw [BL_eq_lift_cube, extremePoints_linear_image _ (blLift_injective d), extremePoints_cube]

lemma blLift_mem_extreme {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    blLift y ∈ Set.extremePoints ℝ (BL d) := by
  rw [extremePoints_BL]
  exact ⟨y, (mem_binaryCube y).mpr hy, rfl⟩

lemma bl_extreme_iff {d : ℕ} (p : Fin (d + 1) → ℝ) :
    p ∈ Set.extremePoints ℝ (BL d) ↔ p ∈ BL d ∧ IsBinaryY p := by
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    rw [extremePoints_BL] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    exact (mem_binaryCube y).mp hy
  · rintro ⟨hp, hy⟩
    have heq : blLift (yproj p) = p := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hp.2.symm
      · rfl
    rw [← heq]
    exact blLift_mem_extreme (yproj p) hy

lemma yproj_extreme_BL (d : ℕ) :
    yproj '' Set.extremePoints ℝ (BL d) = {y : Fin d → ℝ | ∀ i, y i = 0 ∨ y i = 1} := by
  rw [extremePoints_BL, Set.image_image]
  ext y
  simp only [blLiftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    yproj_blLift, Set.image_id', mem_binaryCube, Set.mem_ofPred_eq]

lemma convexHull_binaryCube (d : ℕ) : convexHull ℝ (binaryCube d) = unitCube d := by
  simp only [binaryCube, unitCube, convexHull_pi, convexHull_pair, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]

lemma BL_isPolytope (d : ℕ) : IsPolytope (BL d) := by
  classical
  have hfin : (binaryCube d).Finite := Set.Finite.pi (fun _ => (Set.finite_singleton (1 : ℝ)).insert 0)
  refine ⟨(hfin.image (blLiftLinear d)).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, ← LinearMap.image_convexHull, convexHull_binaryCube]
  exact BL_eq_lift_cube d

end BinaryExtForm.HypercubeRank.LogarithmicProof

namespace BinaryExtForm.HypercubeRank.BitsProof

lemma binary_representation (d m : ℕ) (hm : m < 2 ^ d) :
    ∃ b : Fin d → ℝ, (∀ i, b i = 0 ∨ b i = 1) ∧
      ∑ i : Fin d, (2 : ℝ) ^ (i : ℕ) * b i = (m : ℝ) := by
  induction d generalizing m with
  | zero =>
      have : m = 0 := by simpa using hm
      subst m
      exact ⟨Fin.elim0, by simp, by simp⟩
  | succ d ih =>
      have hdiv : m / 2 < 2 ^ d := by
        apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
        simpa [pow_succ, Nat.mul_comm] using hm
      obtain ⟨b, hb, hsum⟩ := ih (m / 2) hdiv
      refine ⟨Fin.cons (m % 2 : ℕ) b, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => hb j) i
        rcases Nat.mod_two_eq_zero_or_one m with h | h
        · left; simp [h]
        · right; simp [h]
      · rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, Fin.cons_zero, one_mul, Fin.val_succ, Fin.cons_succ]
        calc
          _ = (m % 2 : ℕ) + 2 * (∑ i : Fin d, (2 : ℝ) ^ (i : ℕ) * b i) := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [pow_succ]
            ring
          _ = (m : ℝ) := by rw [hsum]; exact_mod_cast Nat.mod_add_div m 2


end BinaryExtForm.HypercubeRank.BitsProof

namespace BinaryExtForm.HypercubeRank.LogarithmicProof

lemma binary_sum_nat {d : ℕ} (y : Fin d → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    ∃ m : ℕ, m + 1 ≤ 2 ^ d ∧ ∑ i : Fin d, (2 : ℝ) ^ (i : ℕ) * y i = (m : ℝ) := by
  classical
  let b : Fin d → ℕ := fun i => if y i = 1 then 1 else 0
  have hb (i : Fin d) : (b i : ℝ) = y i := by
    rcases hy i with h | h <;> simp [b, h]
  let m : ℕ := ∑ i : Fin d, 2 ^ (i : ℕ) * b i
  refine ⟨m, ?_, ?_⟩
  · have hm : m ≤ ∑ i : Fin d, 2 ^ (i : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [b]
      split_ifs <;> simp
    have hsum : (∑ i : Fin d, 2 ^ (i : ℕ)) = 2 ^ d - 1 := by
      rw [Fin.sum_univ_eq_sum_range]
      simpa using Nat.geomSum_eq (by decide : 2 ≤ 2) d
    rw [hsum] at hm
    have hpos := Nat.two_pow_pos d
    omega
  · dsimp [m]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hb]

lemma binary_x_image (d : ℕ) :
    (fun p : Fin (d + 1) → ℝ => p 0) '' {p | p ∈ BL d ∧ IsBinaryY p} =
      {t : ℝ | ∃ m : ℕ, m + 1 ≤ 2 ^ d ∧ t = m} := by
  ext t
  constructor
  · rintro ⟨p, ⟨hp, hy⟩, rfl⟩
    obtain ⟨m, hm, hsum⟩ := binary_sum_nat (yproj p) hy
    exact ⟨m, hm, hp.2.trans hsum⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨y, hy, hsum⟩ := BitsProof.binary_representation d m (by omega)
    exact ⟨blLift y, ⟨(blLift_mem_extreme y hy).1, hy⟩, hsum⟩

lemma xproj_extreme_BL (d : ℕ) :
    (fun p : Fin (d + 1) → ℝ => p 0) '' Set.extremePoints ℝ (BL d) =
      {t : ℝ | ∃ m : ℕ, m + 1 ≤ 2 ^ d ∧ t = m} := by
  have heq : Set.extremePoints ℝ (BL d) = {p | p ∈ BL d ∧ IsBinaryY p} :=
    Set.ext bl_extreme_iff
  rw [heq]
  exact binary_x_image d

end BinaryExtForm.HypercubeRank.LogarithmicProof

namespace BinaryExtForm.HypercubeRank
open LogarithmicProof

theorem bl_isHypercubeBinarization (d : ℕ) (hd : 0 < d) :
    IsHypercubeBinarization d (BL d) := by
  have htwo : 2 ≤ 2 ^ d := by
    calc
      2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  refine ⟨⟨BL_isPolytope d, by omega, fun p hp => hp.1, ?_⟩,
    yproj_extreme_BL d, xproj_extreme_BL d⟩
  rw [binary_x_image]
  ext t
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, by omega, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, by omega, rfl⟩

end BinaryExtForm.HypercubeRank

namespace BinaryExtForm.HypercubeRank.BitsProof

lemma dvd_succ_iff_mod (a t : ℕ) : 2 ^ t ∣ a + 1 ↔ a % 2 ^ t = 2 ^ t - 1 := by
  have hp : 0 < 2 ^ t := Nat.two_pow_pos t
  have hr := Nat.mod_lt a hp
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [← Nat.mod_add_mod a (2 ^ t) 1]
  constructor
  · intro h
    by_contra hn
    have hl : a % 2 ^ t + 1 < 2 ^ t := by omega
    rw [Nat.mod_eq_of_lt hl] at h
    omega
  · intro h
    have heq : a % 2 ^ t + 1 = 2 ^ t := by omega
    rw [heq, Nat.mod_self]

lemma dvd_succ_iff_bits (a t : ℕ) :
    2 ^ t ∣ a + 1 ↔ ∀ i < t, a.testBit i = true := by
  rw [dvd_succ_iff_mod]
  constructor
  · intro h i hi
    have hh := congrArg (fun n : ℕ => n.testBit i) h
    simpa [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hi] using hh
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < t
    · simp [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hi, h i hi]
    · simp [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hi]

end BinaryExtForm.HypercubeRank.BitsProof

set_option autoImplicit false

namespace BinaryExtForm.HypercubeRank.BitsProof

noncomputable def digit {d : ℕ} (p : Fin (d + 1) → ℝ) (i : Fin d) : ℕ :=
  if p i.succ = 1 then 1 else 0

noncomputable def label {d : ℕ} (p : Fin (d + 1) → ℝ) : ℕ :=
  ∑ i : Fin d, 2 ^ (i : ℕ) * digit p i

noncomputable def low {d : ℕ} (p : Fin (d + 1) → ℝ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < t), 2 ^ (i : ℕ) * digit p i

noncomputable def high {d : ℕ} (p : Fin (d + 1) → ℝ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (i : ℕ) < t), 2 ^ (i : ℕ) * digit p i

lemma label_eq {d : ℕ} {p : Fin (d + 1) → ℝ} (hp : p ∈ BL d) (hb : IsBinaryY p) :
    (label p : ℝ) = p 0 := by
  rw [hp.2]
  simp only [label, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro i _
  rcases hb i with h | h <;> simp [digit, h]

lemma label_split {d : ℕ} (p : Fin (d + 1) → ℝ) (t : ℕ) :
    low p t + high p t = label p := by
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma high_dvd {d : ℕ} (p : Fin (d + 1) → ℝ) (t : ℕ) : 2 ^ t ∣ high p t := by
  apply Finset.dvd_sum
  intro i hi
  have hti : t ≤ (i : ℕ) := Nat.le_of_not_gt (Finset.mem_filter.mp hi).2
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hti) _

lemma low_lt {d : ℕ} (p : Fin (d + 1) → ℝ) (t : ℕ) : low p t < 2 ^ t := by
  classical
  let S := Finset.univ.filter (fun i : Fin d => (i : ℕ) < t)
  have hbound : low p t ≤ ∑ i ∈ S, 2 ^ (i : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    unfold digit
    split_ifs <;> simp
  have himage : ∑ i ∈ S, 2 ^ (i : ℕ) = ∑ i ∈ S.image Fin.val, 2 ^ i := by
    rw [Finset.sum_image]
    intro i hi j hj heq
    exact Fin.ext heq
  have hsub : S.image Fin.val ⊆ Finset.range t := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  have hgeom : ∑ i ∈ Finset.range t, 2 ^ i = 2 ^ t - 1 := by
    simpa using Nat.geomSum_eq (by omega : 2 ≤ 2) t
  have hh := Finset.sum_le_sum_of_subset hsub (f := fun i : ℕ => 2 ^ i)
  rw [← himage, hgeom] at hh
  have hp := Nat.two_pow_pos t
  omega

lemma high_eq_of_differs {d : ℕ} {u v : Fin (d + 1) → ℝ} {i : Fin d}
    (h : DiffersOnlyAt u v i) (t : ℕ) (hi : (i : ℕ) < t) : high u t = high v t := by
  apply Finset.sum_congr rfl
  intro k hk
  have hki : k ≠ i := by intro heq; subst k; exact (Finset.mem_filter.mp hk).2 hi
  simp [digit, h.2 k hki]

lemma no_crossing_block (a H L U t : ℕ) (hH : 2 ^ t ∣ H) (ha : 2 ^ t ∣ a + 1)
    (hlo : H + L ≤ a) (hup : a + 1 ≤ H + U) (hu : U < 2 ^ t) : False := by
  have hpos : 0 < a + 1 - H := by omega
  have hdiv : 2 ^ t ∣ a + 1 - H := Nat.dvd_sub ha hH
  have hle := Nat.le_of_dvd hpos hdiv
  omega

lemma not_typeHit_of_dvd {d ℓ : ℕ} (α : Fin ℓ → ℕ) (t : ℕ)
    (hdiv : ∀ j, 2 ^ t ∣ α j + 1) (i : Fin d) (hi : (i : ℕ) < t) :
    ¬ typeHit (BL d) α i := by
  rintro ⟨j, u, hu, v, hv, hdiff, hua, hav⟩
  obtain ⟨huB, hub⟩ := (LogarithmicProof.bl_extreme_iff u).mp hu
  obtain ⟨hvB, hvb⟩ := (LogarithmicProof.bl_extreme_iff v).mp hv
  have hulabel : label u ≤ α j := by exact_mod_cast (show (label u : ℝ) ≤ α j by rw [label_eq huB hub]; exact hua)
  have hvlabel : α j + 1 ≤ label v := by exact_mod_cast (show (α j : ℝ) + 1 ≤ (label v : ℝ) by rw [label_eq hvB hvb]; exact hav)
  have heq := high_eq_of_differs hdiff t hi
  apply no_crossing_block (α j) (high u t) (low u t) (low v t) t (high_dvd u t) (hdiv j)
  · rw [Nat.add_comm, label_split]
    exact hulabel
  · rw [heq, Nat.add_comm (high v t), label_split]
    exact hvlabel
  · exact low_lt v t

end BinaryExtForm.HypercubeRank.BitsProof

set_option autoImplicit true
namespace BinaryExtForm.HypercubeRank.FiberProof

lemma binarization_convex {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) : Convex ℝ B := by
  obtain ⟨S,hS⟩ := hB.1
  rw [hS]
  exact convex_convexHull ℝ _

lemma binary_label {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {p : Fin (d + 1) → ℝ}
    (hp : p ∈ B) (hb : IsBinaryY p) : ∃ m : ℕ, m ≤ k ∧ p 0 = m := by
  have hh : p 0 ∈ (fun p => p 0) '' {p | p ∈ B ∧ IsBinaryY p} := ⟨p,⟨hp,hb⟩,rfl⟩
  rw [hB.2.2.2] at hh
  exact hh

lemma binary_fiber_no_lt {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : ¬ u 0 < v 0 := by
  intro hlt
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  obtain ⟨a,ha,hua⟩ := binary_label hB hu hb
  obtain ⟨b,hbnd,hvb⟩ := binary_label hB hv hb'
  have hab : a < b := by exact_mod_cast (show (a:ℝ)<b by simpa [hua,hvb] using hlt)
  have hdiff : 1 ≤ v 0-u 0 := by
    have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
    rw [hua,hvb]
    linarith
  let t : ℝ := 1 / (2*(v 0-u 0))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by linarith : 0 < 2*(v 0-u 0))).mpr; linarith
  let p : Fin (d+1) → ℝ := (1-t) • u + t • v
  have hp : p ∈ B := binarization_convex hB hu hv (sub_nonneg.mpr ht1) ht.le (by ring)
  have hpy (i : Fin d) : p i.succ = u i.succ := by
    have hh : u i.succ = v i.succ := congrFun hy i
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [← hh]
    ring
  have hpb : IsBinaryY p := by
    intro i
    rw [hpy]
    exact hb i
  obtain ⟨m,hm,hpm⟩ := binary_label hB hp hpb
  have hp0 : p 0 = u 0+1/2 := by
    simp only [p,Pi.add_apply,Pi.smul_apply,smul_eq_mul,t]
    field_simp
    ring
  have ham : a < m := by
    have hh : (a : ℝ) < m := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  have hma : m < a+1 := by
    have hh : (m : ℝ) < (a : ℝ) + 1 := by rw [← hpm,hp0,hua]; norm_num
    exact_mod_cast hh
  omega

lemma binary_fiber_unique {d k : ℕ} {B : Set (Fin (d + 1) → ℝ)}
    (hB : IsBinarization d k B) {u v : Fin (d + 1) → ℝ}
    (hu : u ∈ B) (hv : v ∈ B) (hb : IsBinaryY u)
    (hy : yproj u = yproj v) : u = v := by
  have hb' : IsBinaryY v := by
    intro i
    have heq : u i.succ = v i.succ := congrFun hy i
    rw [← heq]
    exact hb i
  have hx : u 0 = v 0 := le_antisymm
    (le_of_not_gt (binary_fiber_no_lt hB hv hu hb' hy.symm))
    (le_of_not_gt (binary_fiber_no_lt hB hu hv hb hy))
  ext i
  refine Fin.cases hx (fun j => congrFun hy j) i

end BinaryExtForm.HypercubeRank.FiberProof

namespace BinaryExtForm.HypercubeRank.FiberProof

lemma cube_labeling {d : ℕ} (B : Set (Fin (d+1) → ℝ))
    (hB : IsHypercubeBinarization d B) :
    ∃ (p : (Fin d → Bool) → (Fin (d+1) → ℝ)) (e : (Fin d → Bool) ≃ Fin (2^d)),
      (∀ y, p y ∈ Set.extremePoints ℝ B) ∧
      (∀ y i, p y i.succ = if y i then 1 else 0) ∧
      (∀ y, p y 0 = ((e y).val : ℝ)) := by
  classical
  have hp_exists (y : Fin d → Bool) : ∃ p ∈ Set.extremePoints ℝ B,
      ∀ i, p i.succ = if y i then 1 else 0 := by
    have hy : (fun i => if y i then (1:ℝ) else 0) ∈
        {y : Fin d → ℝ | ∀ i, y i=0 ∨ y i=1} := by
      intro i
      cases y i <;> simp
    rw [← hB.2.1] at hy
    obtain ⟨p,hp,heq⟩ := hy
    exact ⟨p,hp,fun i => congrFun heq i⟩
  choose p hp hpy using hp_exists
  have hn_exists (y : Fin d → Bool) : ∃ m : ℕ, m < 2^d ∧ p y 0 = m := by
    have hh : p y 0 ∈ (fun p => p 0) '' Set.extremePoints ℝ B := ⟨p y,hp y,rfl⟩
    rw [hB.2.2] at hh
    obtain ⟨m,hm,heq⟩ := hh
    exact ⟨m,by omega,heq⟩
  choose n hn hpn using hn_exists
  let f : (Fin d → Bool) → Fin (2^d) := fun y => ⟨n y,hn y⟩
  have hsurj : Function.Surjective f := by
    intro m
    have hm : (m.val : ℝ) ∈ {t : ℝ | ∃ n : ℕ, n+1≤2^d ∧ t=n} :=
      ⟨m.val,by omega,rfl⟩
    rw [← hB.2.2] at hm
    obtain ⟨v,hv,hvm⟩ := hm
    have hvbin : IsBinaryY v := by
      have hh : yproj v ∈ yproj '' Set.extremePoints ℝ B := ⟨v,hv,rfl⟩
      rw [hB.2.1] at hh
      exact hh
    let y : Fin d → Bool := fun i => decide (v i.succ=1)
    have hycoord (i : Fin d) : (if y i then (1:ℝ) else 0) = v i.succ := by
      rcases hvbin i with hz|ho
      · simp [y,hz]
      · simp [y,ho]
    have hyp : yproj (p y) = yproj v := by
      ext i
      exact (hpy y i).trans (hycoord i)
    have hpbin : IsBinaryY (p y) := by
      intro i
      rw [hpy]
      cases y i <;> simp
    have hpv : p y = v := binary_fiber_unique hB.1 (hp y).1 hv.1 hpbin hyp
    refine ⟨y,?_⟩
    apply Fin.ext
    change n y = m.val
    have hh : (n y : ℝ) = (m.val : ℝ) := by
      rw [← hpn y,hpv]
      exact hvm
    exact_mod_cast hh
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj,by simp⟩
  exact ⟨p,Equiv.ofBijective f hbij,hp,hpy,hpn⟩

end BinaryExtForm.HypercubeRank.FiberProof



set_option autoImplicit false

namespace BinaryExtForm.HypercubeRank.DivisibilityProof

lemma predicate_piecewise_iff {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (P : (ι → Bool) → Prop)
    (hinv : ∀ i ∈ F, ∀ x b, P (Function.update x i b) ↔ P x)
    (z x : ι → Bool) : P (F.piecewise z x) ↔ P x := by
  revert hinv
  induction F using Finset.induction_on with
  | empty => intro _; simp
  | @insert i F hi ih =>
    intro hinv
    rw [Finset.piecewise_insert]
    exact (hinv i (Finset.mem_insert_self _ _) _ _).trans
      (ih (fun k hk => hinv k (Finset.mem_insert_of_mem hk)))

noncomputable def cubeSplit {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (u : {i // i ∈ F} → Bool) (w : {i // i ∉ F} → Bool) (i : ι) : Bool :=
  if hi : i ∈ F then u ⟨i, hi⟩ else w ⟨i, hi⟩

lemma free_coordinates_dvd_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (P : (ι → Bool) → Prop) [DecidablePred P]
    (hinv : ∀ i ∈ F, ∀ x b, P (Function.update x i b) ↔ P x) :
    2^F.card ∣ Fintype.card {x : ι → Bool // P x} := by
  classical
  let Q : ({i // i ∉ F} → Bool) → Prop := fun w => P (cubeSplit F (fun _ => false) w)
  have hsplit (u : {i // i ∈ F} → Bool) (w : {i // i ∉ F} → Bool) :
      P (cubeSplit F u w) ↔ Q w := by
    have he : F.piecewise (fun _ => false) (cubeSplit F u w) =
        cubeSplit F (fun _ => false) w := by
      ext i
      by_cases hi : i ∈ F <;> simp [Finset.piecewise, cubeSplit, hi]
    exact ((predicate_piecewise_iff F P hinv (fun _ => false) (cubeSplit F u w)).symm).trans
      (by rw [he])
  have hreconstruct (x : ι → Bool) :
      cubeSplit F (fun i => x i) (fun i => x i) = x := by
    ext i
    by_cases hi : i ∈ F <;> simp [cubeSplit, hi]
  let e : {x : ι → Bool // P x} ≃
      ({i // i ∈ F} → Bool) × {w : {i // i ∉ F} → Bool // Q w} := {
    toFun := fun x => ⟨(fun i => x.val i), ⟨(fun i => x.val i), by
      apply (hsplit (fun i => x.val i) (fun i => x.val i)).mp
      rw [hreconstruct]
      exact x.property⟩⟩
    invFun := fun z => ⟨cubeSplit F z.1 z.2.val, (hsplit z.1 z.2.val).mpr z.2.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact hreconstruct x.val
    right_inv := by
      rintro ⟨u,w⟩
      apply Prod.ext
      · funext i
        simp [cubeSplit, i.property]
      · apply Subtype.ext
        funext i
        simp [cubeSplit, i.property]
  }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  exact ⟨Fintype.card {w : {i // i ∉ F} → Bool // Q w}, hc⟩

end BinaryExtForm.HypercubeRank.DivisibilityProof

namespace BinaryExtForm.HypercubeRank.DivisibilityProof

theorem divisibility_of_cube_labeling {d ℓ : ℕ} (B : Set (Fin (d+1) → ℝ))
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2^d)
    (p : (Fin d → Bool) → (Fin (d+1) → ℝ))
    (e : (Fin d → Bool) ≃ Fin (2^d))
    (hp : ∀ y, p y ∈ Set.extremePoints ℝ B)
    (hy : ∀ y i, p y i.succ = if y i then 1 else 0)
    (hlabel : ∀ y, p y 0 = ((e y).val : ℝ)) :
    ∀ j, 2^fB B α ∣ α j + 1 := by
  classical
  intro j
  let F : Finset (Fin d) := Finset.univ.filter (fun i => ¬typeHit B α i)
  let P : (Fin d → Bool) → Prop := fun y => (e y).val ≤ α j
  have hinv : ∀ i ∈ F, ∀ y b, P (Function.update y i b) ↔ P y := by
    intro i hi y b
    have hfree : ¬typeHit B α i := (Finset.mem_filter.mp hi).2
    by_cases hsame : b = y i
    · subst b
      simp
    let z : Fin d → Bool := Function.update y i b
    have hdiff : DiffersOnlyAt (p z) (p y) i := by
      constructor
      · simp only [hy, z, Function.update_self]
        cases b <;> cases hyi : y i <;> simp_all
      · intro k hki
        rw [hy, hy]
        simp [z, Function.update_of_ne hki]
    change P z ↔ P y
    constructor
    · intro hz
      by_contra hy'
      apply hfree
      refine ⟨j, p z, hp z, p y, hp y, hdiff, ?_, ?_⟩
      · rw [hlabel]
        exact_mod_cast hz
      · rw [hlabel]
        have hn : α j + 1 ≤ (e y).val := by dsimp [P] at hy'; omega
        exact_mod_cast hn
    · intro hy'
      by_contra hz
      apply hfree
      refine ⟨j, p y, hp y, p z, hp z, ⟨hdiff.1.symm, fun k hk => (hdiff.2 k hk).symm⟩, ?_, ?_⟩
      · rw [hlabel]
        exact_mod_cast hy'
      · rw [hlabel]
        have hn : α j + 1 ≤ (e z).val := by dsimp [P] at hz; omega
        exact_mod_cast hn
  let ecut : {y : Fin d → Bool // P y} ≃ Fin (α j + 1) := {
    toFun := fun y => ⟨(e y.val).val, by have := y.property; dsimp [P] at this; omega⟩
    invFun := fun m => ⟨e.symm ⟨m.val, by have := hα j; have := m.isLt; omega⟩, by
      dsimp [P]
      simp only [Equiv.apply_symm_apply]
      have := m.isLt
      omega⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply e.injective
      simp only [Equiv.apply_symm_apply]
    right_inv := by
      intro m
      apply Fin.ext
      simp only [Equiv.apply_symm_apply]
  }
  have hc := Fintype.card_congr ecut
  simp only [Fintype.card_fin] at hc
  rw [← hc]
  change 2^F.card ∣ Fintype.card {y : Fin d → Bool // P y}
  exact free_coordinates_dvd_card F P hinv

end BinaryExtForm.HypercubeRank.DivisibilityProof

open BinaryExtForm.HypercubeRank

theorem BinaryExtForm.HypercubeRank.BitsProof.general_divisibility {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d) :
    ∀ j, 2 ^ fB B α ∣ α j + 1 := by
  obtain ⟨p,e,hp,hy,hlabel⟩ := FiberProof.cube_labeling B hB
  exact DivisibilityProof.divisibility_of_cube_labeling B α hα p e hp hy hlabel

set_option autoImplicit false
namespace BinaryExtForm.HypercubeRank.BitsProof

lemma exponent_lt_dimension {d ℓ : ℕ} (hℓ : 0 < ℓ) (α : Fin ℓ → ℕ)
    (hα : ∀ j, α j + 2 ≤ 2 ^ d) (t : ℕ) (ht : ∀ j, 2 ^ t ∣ α j + 1) : t < d := by
  let j : Fin ℓ := ⟨0, hℓ⟩
  have hle := Nat.le_of_dvd (Nat.succ_pos (α j)) (ht j)
  by_contra hn
  have hdt : d ≤ t := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hdt
  have := hα j
  omega

lemma exponent_le_fB {d ℓ : ℕ} (hℓ : 0 < ℓ) (α : Fin ℓ → ℕ)
    (hα : ∀ j, α j + 2 ≤ 2 ^ d) (t : ℕ) (ht : ∀ j, 2 ^ t ∣ α j + 1) :
    t ≤ fB (BL d) α := by
  classical
  have htd := (exponent_lt_dimension hℓ α hα t ht).le
  let f : Fin t → Fin d := fun i => ⟨i.val, lt_of_lt_of_le i.isLt htd⟩
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := Finset.univ.filter (fun i : Fin d => ¬typeHit (BL d) α i)) f
    (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      not_typeHit_of_dvd α t ht (f i) i.isLt⟩)
    (fun i _ j _ hij => Fin.ext (congrArg (fun k : Fin d => k.val) hij))
  simpa only [Finset.card_univ, Fintype.card_fin, fB] using hcard

end BinaryExtForm.HypercubeRank.BitsProof

open BinaryExtForm.HypercubeRank

theorem BinaryExtForm.HypercubeRank.logarithmic_maximal_exponent {d ℓ : ℕ} (hℓ : 0 < ℓ) (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d) :
    IsGreatest {t : ℕ | ∀ j, 2 ^ t ∣ α j + 1} (fB (BL d) α) := by
  have hd : 0 < d := by
    have := hα ⟨0, hℓ⟩
    by_contra hn
    have : d = 0 := by omega
    subst d
    simp at *
  refine ⟨BitsProof.general_divisibility (BL d) (bl_isHypercubeBinarization d hd) α hα, ?_⟩
  intro t ht
  exact BitsProof.exponent_le_fB hℓ α hα t ht


namespace BinaryExtForm.HypercubeRank.RootProof
open Disjunctive.HigherDim

lemma lpr_empty {n : ℕ} (H : Finset (Fin n)) : lpr (∅ : Set (Fin n → ℝ)) H = 0 := by
  apply Nat.le_zero.mp
  apply csInf_le'
  refine ⟨[],by simp,rfl,?_⟩
  simp [IteratedSplit,intHull]

lemma rk_no_slices {d : ℕ} (B : Set (Fin (d+1) → ℝ)) (xbar : Fin 0 → ℝ) :
    rk B xbar = 0 := by
  simp [rk,lpr_empty]

lemma dimension_pos {d : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsHypercubeBinarization d B) : 0 < d := by
  by_contra h
  have hd : d=0 := by omega
  have hpos := hB.1.2.1
  simp [hd] at hpos

lemma root_of_logarithmic {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ))
    (hB : IsHypercubeBinarization d B) (hBL : IsHypercubeBinarization d (BL d))
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar xbarL : Fin ℓ → ℝ)
    (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1)
    (hxL : ∀ j, (α j : ℝ) < xbarL j ∧ xbarL j < α j + 1) :
    rk (BL d) xbarL ≤ rk B xbar := by
  by_cases hℓ : ℓ=0
  · subst ℓ
    simp [rk_no_slices]
  · have hpos : 0 < ℓ := by omega
    rw [corollary_4_19 B hB α hα xbar hx,
      corollary_4_19 (BL d) hBL α hα xbarL hxL]
    exact Nat.sub_le_sub_left ((logarithmic_maximal_exponent hpos α hα).2 (BitsProof.general_divisibility B hB α hα)) d

end BinaryExtForm.HypercubeRank.RootProof
open BinaryExtForm.HypercubeRank BinaryExtForm.HypercubeRank.RootProof

theorem solution {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar xbarL : Fin ℓ → ℝ)
    (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1)
    (hxL : ∀ j, (α j : ℝ) < xbarL j ∧ xbarL j < α j + 1) :
    rk (BL d) xbarL ≤ rk B xbar := by
  exact root_of_logarithmic B hB (bl_isHypercubeBinarization d (dimension_pos hB))
    α hα xbar xbarL hx hxL
