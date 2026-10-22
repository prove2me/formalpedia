-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T03:01:50.838083+00:00
-- url     : https://prove2.me/submissions/a6394e8b-230f-4159-8433-827b4ced360a

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix
open Matrix
open scoped BigOperators
noncomputable section
namespace NTScalingProof
open ConicQuadIPM.NTScaling
open ConicQuadIPM.Complementarity (ConeKind coord tailSq e1)

def qform {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  x ⬝ᵥ (Q *ᵥ x)

def signature {d : ℕ} (a : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (2 : ℝ) • vecMulVec a a - 1

def boost {d : ℕ} (a w : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  -signature a + (1 + a ⬝ᵥ w)⁻¹ • vecMulVec (a + w) (a + w)

def anchor (kind : ConeKind) (d : ℕ) : Fin d → ℝ :=
  Tmat kind d *ᵥ e1

end NTScalingProof

open Matrix
open scoped BigOperators
noncomputable section
namespace NTScalingProof
open ConicQuadIPM.NTScaling
open ConicQuadIPM.Complementarity (ConeKind coord tailSq e1)

theorem coord_eq {d : ℕ} (v : Fin d → ℝ) (i : Fin d) : coord v i.val = v i := by
  classical
  simp [coord, Fin.val_inj]

theorem e1_dot {d : ℕ} (v : Fin d → ℝ) : e1 ⬝ᵥ v = coord v 0 := by
  classical
  simp [e1, coord, dotProduct, ite_mul]

private theorem head_sq {d : ℕ} (x : Fin d → ℝ) (k : ℕ) :
    (∑ i, if i.val = k then (x i)^2 else 0) = (coord x k)^2 := by
  classical
  by_cases hk : k < d
  · have he (i : Fin d) : i.val = k ↔ i = ⟨k, hk⟩ := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; exact congrArg Fin.val h
    simp [coord, he]
  · have he (i : Fin d) : i.val ≠ k := by omega
    simp [coord, he]

private theorem head_mul {d : ℕ} (x : Fin d → ℝ) (k : ℕ) (c : ℝ) :
    (∑ i, if i.val = k then x i * c else 0) = coord x k * c := by
  classical
  simp [coord, Finset.sum_mul, ite_mul]

private theorem quad_mulVec {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    (Qmat .quad d *ᵥ x) i = if i.val = 0 then x i else -x i := by
  classical
  by_cases h : i.val = 0 <;> simp [Qmat, mulVec, dotProduct, ite_mul, h]

private theorem rot_mulVec {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    (Qmat .rot d *ᵥ x) i =
      if i.val = 0 then coord x 1 else if i.val = 1 then coord x 0 else -x i := by
  classical
  by_cases h0 : i.val = 0
  · simp [Qmat, mulVec, dotProduct, h0, coord, ite_mul]
  by_cases h1 : i.val = 1
  · simp [Qmat, mulVec, dotProduct, h1, coord, ite_mul]
  have h2 : 2 ≤ i.val := by omega
  simp [Qmat, mulVec, dotProduct, h0, h1, h2, ite_mul]

theorem qform_quad {d : ℕ} (x : Fin d → ℝ) :
    qform (Qmat .quad d) x = (coord x 0)^2 - tailSq x 1 := by
  classical
  have he (i : Fin d) : x i * (if i.val = 0 then x i else -x i) =
      (if i.val = 0 then (x i)^2 else 0) -
        (if 1 ≤ i.val then (x i)^2 else 0) := by
    by_cases h : i.val = 0
    · simp [h, pow_two]
    · have h1 : 1 ≤ i.val := by omega
      simp [h, h1, pow_two]
  simp only [qform, dotProduct, quad_mulVec, he, Finset.sum_sub_distrib, head_sq]
  rfl

theorem qform_rot {d : ℕ} (x : Fin d → ℝ) :
    qform (Qmat .rot d) x = 2 * coord x 0 * coord x 1 - tailSq x 2 := by
  classical
  have he (i : Fin d) :
      x i * (if i.val = 0 then coord x 1 else if i.val = 1 then coord x 0 else -x i) =
      ((if i.val = 0 then x i * coord x 1 else 0) +
        (if i.val = 1 then x i * coord x 0 else 0)) -
        (if 2 ≤ i.val then (x i)^2 else 0) := by
    by_cases h0 : i.val = 0
    · simp [h0]
    by_cases h1 : i.val = 1
    · simp [h1]
    have h2 : 2 ≤ i.val := by omega
    simp [h0, h1, h2, pow_two]
  simp only [qform, dotProduct, rot_mulVec, he, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, head_mul]
  change coord x 0 * coord x 1 + coord x 1 * coord x 0 - tailSq x 2 = _
  ring

theorem anchor_quad (d : ℕ) : anchor .quad d = e1 := by
  simp [anchor, Tmat]

private theorem anchor_nonneg (d : ℕ) : anchor .nonneg d = e1 := by
  simp [anchor, Tmat]

private theorem anchor_rot_apply (d : ℕ) (hd : 0 < d) (i : Fin d) :
    anchor .rot d i = if i.val < 2 then 1 / Real.sqrt 2 else 0 := by
  classical
  let z : Fin d := ⟨0, hd⟩
  have h : anchor .rot d i = Tmat .rot d i z := by
    unfold anchor mulVec dotProduct
    rw [Finset.sum_eq_single z]
    · simp [e1, z]
    · intro j _ hj
      have hv : j.val ≠ 0 := by intro hv; apply hj; exact Fin.ext hv
      simp [e1, hv]
    · simp
  rw [h]
  by_cases hi : i.val < 2
  · have hi2 : i.val ≤ 1 := by omega
    simp [Tmat, z, hi2]
  · have hiz : i ≠ z := by intro he; subst i; simp [z] at hi
    have hi2 : 1 < i.val := by omega
    have hiz2 : i ≠ ⟨0, hd⟩ := hiz
    simp [Tmat, z, hiz2]

private theorem anchor_rot_dot (d : ℕ) (hd : 0 < d) (x : Fin d → ℝ) :
    anchor .rot d ⬝ᵥ x = (coord x 0 + coord x 1) / Real.sqrt 2 := by
  classical
  have he (i : Fin d) :
      (if i.val < 2 then 1 / Real.sqrt 2 else 0) * x i =
      (if i.val = 0 then x i * (Real.sqrt 2)⁻¹ else 0) +
      (if i.val = 1 then x i * (Real.sqrt 2)⁻¹ else 0) := by
    by_cases h0 : i.val = 0
    · simp [h0]; ring
    by_cases h1 : i.val = 1
    · simp [h1]; ring
    have h2 : ¬ i.val < 2 := by omega
    simp [h0, h1, h2]
  simp only [dotProduct, anchor_rot_apply d hd, he, Finset.sum_add_distrib, head_mul]
  ring

theorem anchor_dot_rot (d : ℕ) (w : Fin d → ℝ) :
    anchor .rot d ⬝ᵥ w = e1 ⬝ᵥ (Tmat .rot d *ᵥ w) := by
  have ht : (Tmat .rot d).IsSymm := by
    ext i j
    simp only [Tmat, transpose_apply, of_apply]
    simp only [and_comm, eq_comm]
  rw [anchor, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, ht.eq, dotProduct_comm]

theorem anchor_unit (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d) :
    anchor kind d ⬝ᵥ anchor kind d = 1 := by
  classical
  cases kind with
  | nonneg =>
    have hd := hwf.1 rfl
    subst d
    simp [anchor, Tmat, e1, dotProduct]
  | quad =>
    have hd : 0 < d := hwf.2.1 rfl
    rw [anchor_quad, e1_dot, coord_eq e1 ⟨0, hd⟩]
    simp [e1]
  | rot =>
    have hd : 2 ≤ d := hwf.2.2 rfl
    have hd0 : 0 < d := by omega
    have h0 : coord (anchor .rot d) 0 = 1 / Real.sqrt 2 := by
      rw [coord_eq (anchor .rot d) ⟨0, hd0⟩, anchor_rot_apply d hd0]; norm_num
    have h1 : coord (anchor .rot d) 1 = 1 / Real.sqrt 2 := by
      rw [coord_eq (anchor .rot d) ⟨1, hd⟩, anchor_rot_apply d hd0]; norm_num
    rw [anchor_rot_dot d hd0, h0, h1]
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
    nlinarith

theorem qmat_eq_signature (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d) :
    Qmat kind d = signature (anchor kind d) := by
  classical
  cases kind with
  | nonneg =>
    have hd := hwf.1 rfl
    subst d
    ext i j
    fin_cases i; fin_cases j
    norm_num [Qmat, signature, anchor, Tmat, e1, vecMulVec]
  | quad =>
    rw [anchor_quad]
    ext i j
    by_cases hij : i = j
    · subst j; by_cases hi : i.val = 0 <;> norm_num [Qmat, signature, e1, vecMulVec, hi]
    · have hboth : ¬ (i.val = 0 ∧ j.val = 0) := by
        rintro ⟨hi, hj⟩; exact hij (Fin.ext (hi.trans hj.symm))
      by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
        simp_all [Qmat, signature, e1, vecMulVec]
  | rot =>
    have hd : 0 < d := by have := hwf.2.2 rfl; omega
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hc : 2 * ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) = 1 := by
      field_simp; nlinarith
    ext i j
    simp only [signature, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      vecMulVec_apply, anchor_rot_apply d hd, Matrix.one_apply, Qmat, of_apply]
    by_cases hij : i = j
    · subst j
      have hcross : ¬ (i.val = 0 ∧ i.val = 1 ∨ i.val = 1 ∧ i.val = 0) := by omega
      by_cases hi : i.val < 2
      · have hn : ¬ 2 ≤ i.val := by omega
        simp_all
        split_ifs <;> norm_num <;> omega
      · have hn : 2 ≤ i.val := by omega
        simp_all
        split_ifs <;> norm_num <;> omega
    · by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
      · have hne : i.val ≠ j.val := by intro h; exact hij (Fin.ext h)
        have hcross : i.val = 0 ∧ j.val = 1 ∨ i.val = 1 ∧ j.val = 0 := by omega
        simp_all
      · have hcross : ¬ (i.val = 0 ∧ j.val = 1 ∨ i.val = 1 ∧ j.val = 0) := by omega
        simp_all
        split_ifs <;> norm_num <;> omega
      · have hcross : ¬ (i.val = 0 ∧ j.val = 1 ∨ i.val = 1 ∧ j.val = 0) := by omega
        simp_all
        split_ifs <;> norm_num <;> omega
      · have hcross : ¬ (i.val = 0 ∧ j.val = 1 ∨ i.val = 1 ∧ j.val = 0) := by omega
        simp_all
        split_ifs <;> norm_num <;> omega

theorem qform_pos (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x : Fin d → ℝ) (hx : inConeInt kind x) : 0 < qform (Qmat kind d) x := by
  cases kind with
  | nonneg =>
    have hd := hwf.1 rfl
    subst d
    have hx0 : 0 < coord x 0 := hx
    have he : qform (Qmat .nonneg 1) x = (coord x 0)^2 := by
      simp [qform, Qmat, coord, dotProduct, pow_two]
    rw [he]
    exact sq_pos_of_pos hx0
  | quad =>
    rw [qform_quad]
    exact sub_pos.mpr hx.1
  | rot =>
    rw [qform_rot]
    exact sub_pos.mpr hx.1

theorem anchor_dot_pos (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x : Fin d → ℝ) (hx : inConeInt kind x) : 0 < anchor kind d ⬝ᵥ x := by
  cases kind with
  | nonneg =>
    rw [anchor_nonneg, e1_dot]
    exact hx
  | quad =>
    rw [anchor_quad, e1_dot]
    exact hx.2
  | rot =>
    have hd : 0 < d := by have := hwf.2.2 rfl; omega
    rw [anchor_rot_dot d hd]
    exact div_pos (add_pos hx.2.1 hx.2.2) (Real.sqrt_pos.2 (by norm_num))

end NTScalingProof

open Matrix

namespace NTScalingProof

variable {d : ℕ}

theorem outer_apply (u v z : Fin d → ℝ) :
    vecMulVec u v *ᵥ z = (v ⬝ᵥ z) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

theorem signature_apply (a z : Fin d → ℝ) :
    signature a *ᵥ z = (2 * (a ⬝ᵥ z)) • a - z := by
  simp [signature, sub_mulVec, smul_mulVec, outer_apply, smul_smul]

theorem signature_symm (a : Fin d → ℝ) : (signature a).IsSymm := by
  show (signature a)ᵀ = signature a
  simp [signature]

theorem signature_sq (a : Fin d → ℝ) (ha : a ⬝ᵥ a = 1) :
    signature a * signature a = 1 := by
  apply ext_of_mulVec_single
  intro j
  simp only [← mulVec_mulVec, signature_apply, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, ha, one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem signature_anchor (a : Fin d → ℝ) (ha : a ⬝ᵥ a = 1) :
    signature a *ᵥ a = a := by
  rw [signature_apply, ha]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem qform_signature (a x : Fin d → ℝ) :
    qform (signature a) x = 2 * (a ⬝ᵥ x)^2 - x ⬝ᵥ x := by
  rw [qform, signature_apply, dotProduct_sub, dotProduct_smul, dotProduct_comm x a]
  simp only [smul_eq_mul]
  ring

theorem boost_apply (a w z : Fin d → ℝ) :
    boost a w *ᵥ z = z - (2 * (a ⬝ᵥ z)) • a +
      ((1 + a ⬝ᵥ w)⁻¹ * (a ⬝ᵥ z + w ⬝ᵥ z)) • (a + w) := by
  simp only [boost, add_mulVec, neg_mulVec, smul_mulVec, outer_apply,
    signature_apply, add_dotProduct, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem boost_symm (a w : Fin d → ℝ) : (boost a w).IsSymm := by
  show (boost a w)ᵀ = boost a w
  simp [boost, (signature_symm a).eq]

theorem boost_preserves (a w : Fin d → ℝ) (ha : a ⬝ᵥ a = 1)
    (hw : qform (signature a) w = 1) (hp : 0 < a ⬝ᵥ w) :
    boost a w * signature a * boost a w = signature a := by
  have hden : 1 + a ⬝ᵥ w ≠ 0 := by positivity
  have hww : w ⬝ᵥ w = 2 * (a ⬝ᵥ w)^2 - 1 := by
    rw [qform_signature] at hw
    linarith
  apply ext_of_mulVec_single
  intro j
  simp only [← mulVec_mulVec, boost_apply, signature_apply, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, ha, hww, dotProduct_comm w a]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hden]
  ring

theorem boost_square (a w : Fin d → ℝ) (ha : a ⬝ᵥ a = 1)
    (hw : qform (signature a) w = 1) (hp : 0 < a ⬝ᵥ w) :
    boost a w * boost a w = -signature a + (2 : ℝ) • vecMulVec w w := by
  have hden : 1 + a ⬝ᵥ w ≠ 0 := by positivity
  have hww : w ⬝ᵥ w = 2 * (a ⬝ᵥ w)^2 - 1 := by
    rw [qform_signature] at hw
    linarith
  apply ext_of_mulVec_single
  intro j
  simp only [← mulVec_mulVec, boost_apply, add_mulVec, neg_mulVec, smul_mulVec,
    outer_apply, signature_apply, dotProduct_add, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, ha, hww, dotProduct_comm w a]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hden]
  ring

theorem boost_properties (a w : Fin d → ℝ) (ha : a ⬝ᵥ a = 1)
    (hw : qform (signature a) w = 1) (hp : 0 < a ⬝ᵥ w) :
    (boost a w).PosDef ∧ boost a w * signature a * boost a w = signature a ∧
    boost a w * boost a w = -signature a + (2 : ℝ) • vecMulVec w w := by
  have hb : 0 < 2 * (1 + a ⬝ᵥ w) := by positivity
  let t := Real.sqrt (2 * (1 + a ⬝ᵥ w))
  have ht : 0 < t := Real.sqrt_pos.2 hb
  have ht2 : t^2 = 2 * (1 + a ⬝ᵥ w) := Real.sq_sqrt hb.le
  let r := t⁻¹ • (a + w)
  have har : a ⬝ᵥ r = t⁻¹ * (1 + a ⬝ᵥ w) := by
    simp only [r, dotProduct_smul, dotProduct_add, ha, smul_eq_mul]
  have hww : w ⬝ᵥ w = 2 * (a ⬝ᵥ w)^2 - 1 := by
    rw [qform_signature] at hw
    linarith
  have hr : qform (signature a) r = 1 := by
    rw [qform_signature]
    simp only [r, dotProduct_smul, smul_dotProduct, dotProduct_add, add_dotProduct,
      smul_eq_mul, ha, hww, dotProduct_comm w a]
    field_simp
    nlinarith [ht2]
  have hrp : 0 < a ⬝ᵥ r := by rw [har]; positivity
  have hpres := boost_preserves a r ha hr hrp
  have hsq := boost_square a r ha hr hrp
  have hfactor : boost a r * boost a r = boost a w := by
    rw [hsq]
    unfold boost
    congr 1
    ext i j
    simp only [r, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
      Matrix.smul_apply]
    field_simp
    rw [ht2]
    ring
  have hinj : Function.Injective (boost a r).mulVec := by
    intro x y hxy
    have h := congrArg (fun z => signature a *ᵥ (boost a r *ᵥ (signature a *ᵥ z))) hxy
    simpa only [mulVec_mulVec, ← mul_assoc, hpres, signature_sq a ha, one_mulVec] using h
  have hconj : (boost a r)ᴴ = boost a r := by
    ext i j
    simpa only [conjTranspose_apply, star_trivial] using (boost_symm a r).apply i j
  have hgram : (boost a r)ᴴ * boost a r = boost a w := by
    rw [hconj, hfactor]
  exact ⟨hgram ▸ PosDef.conjTranspose_mul_self (boost a r) hinj,
    boost_preserves a w ha hw hp, boost_square a w ha hw hp⟩

end NTScalingProof

open Matrix
open scoped BigOperators
noncomputable section
namespace NTScalingProof
open ConicQuadIPM.NTScaling
open ConicQuadIPM.Complementarity (ConeKind coord)

private theorem future_dot_pos {d : ℕ} (a x s : Fin d → ℝ)
    (ha : a ⬝ᵥ a = 1) (hx : 0 < qform (signature a) x)
    (hs : 0 < qform (signature a) s) (hxp : 0 < a ⬝ᵥ x)
    (hsp : 0 < a ⬝ᵥ s) : 0 < x ⬝ᵥ s := by
  let u := x - (a ⬝ᵥ x) • a
  let v := s - (a ⬝ᵥ s) • a
  have huu : u ⬝ᵥ u = x ⬝ᵥ x - (a ⬝ᵥ x)^2 := by
    simp only [u, sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, ha, dotProduct_comm x a]
    ring
  have hvv : v ⬝ᵥ v = s ⬝ᵥ s - (a ⬝ᵥ s)^2 := by
    simp only [v, sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, ha, dotProduct_comm s a]
    ring
  have huv : u ⬝ᵥ v = x ⬝ᵥ s - (a ⬝ᵥ x) * (a ⬝ᵥ s) := by
    simp only [u, v, sub_dotProduct, dotProduct_sub, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, ha, dotProduct_comm x a]
    ring
  have hu0 : 0 ≤ u ⬝ᵥ u := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  have hv0 : 0 ≤ v ⬝ᵥ v := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  rw [qform_signature] at hx hs
  have hu : u ⬝ᵥ u < (a ⬝ᵥ x)^2 := by linarith
  have hv : v ⬝ᵥ v < (a ⬝ᵥ s)^2 := by linarith
  have hcs : (u ⬝ᵥ v)^2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
    simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hprod : (u ⬝ᵥ u) * (v ⬝ᵥ v) < (a ⬝ᵥ x)^2 * (a ⬝ᵥ s)^2 :=
    (mul_le_mul_of_nonneg_left hv.le hu0).trans_lt
      (mul_lt_mul_of_pos_right hu (sq_pos_of_pos hsp))
  have hp : 0 < (a ⬝ᵥ x) * (a ⬝ᵥ s) := mul_pos hxp hsp
  by_contra hn
  have ht : u ⬝ᵥ v ≤ -(a ⬝ᵥ x * (a ⬝ᵥ s)) := by linarith
  have hn1 : 0 ≤ -(u ⬝ᵥ v) - (a ⬝ᵥ x) * (a ⬝ᵥ s) := by linarith
  have hn2 : 0 ≤ -(u ⬝ᵥ v) + (a ⬝ᵥ x) * (a ⬝ᵥ s) := by linarith
  nlinarith [mul_nonneg hn1 hn2]

private theorem qform_smul {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (x : Fin d → ℝ) : qform Q (c • x) = c^2 * qform Q x := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem normalization (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s) :
    0 < thetaNT kind d x s ∧
    qform (Qmat kind d) (wNT kind d x s) = 1 ∧
    0 < anchor kind d ⬝ᵥ wNT kind d x s ∧
    (thetaNT kind d x s)^2 •
      ((-Qmat kind d + (2 : ℝ) • vecMulVec (wNT kind d x s) (wNT kind d x s)) *ᵥ x) = s := by
  let a := anchor kind d
  let Q := Qmat kind d
  let A := qform Q x
  let C := qform Q s
  let D := x ⬝ᵥ s
  let t := thetaNT kind d x s
  let K := Real.sqrt (A * C)
  let h := Real.sqrt 2 * Real.sqrt (D + K)
  let y := t⁻¹ • s + t • (Q *ᵥ x)
  let w := wNT kind d x s
  have hQ : Q = signature a := qmat_eq_signature kind d hwf
  have ha : a ⬝ᵥ a = 1 := anchor_unit kind d hwf
  have hA : 0 < A := qform_pos kind d hwf x hx
  have hC : 0 < C := qform_pos kind d hwf s hs
  have hax : 0 < a ⬝ᵥ x := anchor_dot_pos kind d hwf x hx
  have has : 0 < a ⬝ᵥ s := anchor_dot_pos kind d hwf s hs
  have hD : 0 < D := future_dot_pos a x s ha (hQ ▸ hA) (hQ ▸ hC) hax has
  have ht : 0 < t := Real.sqrt_pos.2 (Real.sqrt_pos.2 (div_pos hC hA))
  have ht2 : t^2 = Real.sqrt (C / A) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht4 : (t^2)^2 = C / A := by rw [ht2]; exact Real.sq_sqrt (div_pos hC hA).le
  have ht4A : (t^2)^2 * A = C := (eq_div_iff hA.ne').mp ht4
  have hK : 0 < K := Real.sqrt_pos.2 (mul_pos hA hC)
  have hK2 : K^2 = A * C := Real.sq_sqrt (mul_pos hA hC).le
  have htA : t^2 * A = K := by
    apply (sq_eq_sq₀ (by positivity) hK.le).mp
    nlinarith [congrArg (fun z : ℝ => z * A) ht4A]
  have hCt : C = K * t^2 := by
    nlinarith [congrArg (fun z : ℝ => z * t^2) htA]
  have hitC : (t⁻¹)^2 * C = K := by
    rw [hCt]
    field_simp
  have hh : 0 < h := mul_pos (Real.sqrt_pos.2 (by norm_num)) (Real.sqrt_pos.2 (add_pos hD hK))
  have hh2 : h^2 = 2 * (D + K) := by
    simp only [h, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (add_pos hD hK).le]
  have hwdef : w = h⁻¹ • y := rfl
  have hya : a ⬝ᵥ y = t⁻¹ * (a ⬝ᵥ s) + t * (a ⬝ᵥ x) := by
    simp only [y, hQ, signature_apply, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, ha]
    ring
  have hyq : qform Q y = (t⁻¹)^2 * C + t^2 * A + 2 * D := by
    simp only [y, A, C, D, hQ, qform_signature, signature_apply, dotProduct_add,
      dotProduct_sub, dotProduct_smul, add_dotProduct, sub_dotProduct,
      smul_dotProduct, smul_eq_mul, ha, dotProduct_comm x a, dotProduct_comm s a,
      dotProduct_comm s x]
    field_simp
    ring
  have hwq : qform Q w = 1 := by
    rw [hwdef, qform_smul, hyq, hitC, htA]
    field_simp
    nlinarith [hh2]
  have hwp : 0 < a ⬝ᵥ w := by
    rw [hwdef, dotProduct_smul, hya]
    simp only [smul_eq_mul]
    positivity
  have hwx : 2 * t * (w ⬝ᵥ x) = h := by
    have hQxx : (Q *ᵥ x) ⬝ᵥ x = A := by rw [dotProduct_comm]; rfl
    simp only [hwdef, y, smul_dotProduct, add_dotProduct, smul_eq_mul,
      hQxx, dotProduct_comm s x]
    change 2 * t * (h⁻¹ * (t⁻¹ * D + t * A)) = h
    field_simp
    nlinarith [hh2, htA]
  refine ⟨ht, hwq, hwp, ?_⟩
  change t^2 • ((-Q + (2 : ℝ) • vecMulVec w w) *ᵥ x) = s
  calc
    t^2 • ((-Q + (2 : ℝ) • vecMulVec w w) *ᵥ x) =
        -(t^2 • (Q *ᵥ x)) + (2 * t * (w ⬝ᵥ x)) • (t • w) := by
      simp only [add_mulVec, neg_mulVec, smul_mulVec, outer_apply]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
      ring
    _ = -(t^2 • (Q *ᵥ x)) + h • (t • w) := by rw [hwx]
    _ = s := by
      rw [hwdef]
      ext i
      simp only [y, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
      field_simp
      ring

theorem nonneg_theta_sq (d : ℕ) (hd : d = 1) (x s : Fin d → ℝ)
    (hx : inConeInt .nonneg x) (hs : inConeInt .nonneg s) :
    (thetaNT .nonneg d x s)^2 = coord s 0 / coord x 0 := by
  subst d
  have hx0 : 0 < x 0 := by simpa [inConeInt, inNonnegInt, coord] using hx
  have hs0 : 0 < s 0 := by simpa [inConeInt, inNonnegInt, coord] using hs
  unfold thetaNT
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  simp only [Qmat, one_mulVec, dotProduct, Fin.sum_univ_one]
  rw [← pow_two, ← pow_two]
  rw [← div_pow, Real.sqrt_sq (div_pos hs0 hx0).le]
  simp [coord]

end NTScalingProof

open Matrix

namespace NTScalingProof
open ConicQuadIPM.NTScaling
open ConicQuadIPM.Complementarity (ConeKind)

variable {d : ℕ}

theorem scaling_qform_smul (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : Fin d → ℝ) :
    qform Q (c • x) = c^2 * qform Q x := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem scaling_qform (kind : ConeKind) (d : ℕ) (W : Matrix (Fin d) (Fin d) ℝ)
    (hW : IsScaling kind d W) (z : Fin d → ℝ) :
    qform (Qmat kind d) (W *ᵥ z) = qform (Qmat kind d) z := by
  have hs : W.IsSymm := isHermitian_iff_isSymm.mp hW.1.1
  have hv (y : Fin d → ℝ) : y ᵥ* W = W *ᵥ y := by
    rw [← mulVec_transpose, hs.eq]
  unfold qform
  calc
    (W *ᵥ z) ⬝ᵥ (Qmat kind d *ᵥ (W *ᵥ z)) =
        z ⬝ᵥ (W *ᵥ (Qmat kind d *ᵥ (W *ᵥ z))) := by
      rw [dotProduct_mulVec z W (Qmat kind d *ᵥ (W *ᵥ z)), hv z]
    _ = z ⬝ᵥ (Qmat kind d *ᵥ z) := by
      rw [mulVec_mulVec, mulVec_mulVec, hW.2]

theorem isNT_iff_square (kind : ConeKind) (d : ℕ) (θ : ℝ)
    (W : Matrix (Fin d) (Fin d) ℝ) (x s : Fin d → ℝ)
    (hθ : 0 < θ) (hW : IsScaling kind d W) :
    IsNT kind d θ W x s ↔ θ^2 • ((W * W) *ᵥ x) = s := by
  have hu := (hW.1.smul hθ).isUnit
  have hd : IsUnit (θ • W).det := (isUnit_iff_isUnit_det (θ • W)).mp hu
  have hsq : (θ • W) * (θ • W) = θ^2 • (W * W) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  have hdouble : (θ • W) *ᵥ ((θ • W) *ᵥ x) = θ^2 • ((W * W) *ᵥ x) := by
    rw [mulVec_mulVec, hsq, smul_mulVec]
  have hinverse : (θ • W) *ᵥ ((θ • W)⁻¹ *ᵥ s) = s := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hd, one_mulVec]
  constructor
  · intro h
    have he := congrArg (fun z => (θ • W) *ᵥ z) h.2.2
    change (θ • W) *ᵥ ((θ • W) *ᵥ x) = (θ • W) *ᵥ ((θ • W)⁻¹ *ᵥ s) at he
    rw [hdouble, hinverse] at he
    exact he
  · intro h
    refine ⟨hθ, hW, ?_⟩
    apply (mulVec_injective_iff_isUnit.mpr hu)
    change (θ • W) *ᵥ ((θ • W) *ᵥ x) = (θ • W) *ᵥ ((θ • W)⁻¹ *ᵥ s)
    rw [hdouble, hinverse]
    exact h

theorem theta_necessary (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s)
    (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) (hNT : IsNT kind d θ W x s) :
    θ^2 = Real.sqrt ((s ⬝ᵥ (Qmat kind d *ᵥ s)) / (x ⬝ᵥ (Qmat kind d *ᵥ x))) := by
  have hqx := qform_pos kind d hwf x hx
  have hqs := qform_pos kind d hwf s hs
  have he := (isNT_iff_square kind d θ W x s hNT.1 hNT.2.1).1 hNT
  have hq : qform (Qmat kind d) s = (θ^2)^2 * qform (Qmat kind d) x := by
    rw [← he, scaling_qform_smul, ← mulVec_mulVec,
      scaling_qform kind d W hNT.2.1, scaling_qform kind d W hNT.2.1]
  have hr : qform (Qmat kind d) s / qform (Qmat kind d) x = (θ^2)^2 := by
    apply (div_eq_iff hqx.ne').2
    nlinarith [hq]
  change θ^2 = Real.sqrt (qform (Qmat kind d) s / qform (Qmat kind d) x)
  symm
  exact (Real.sqrt_eq_iff_eq_sq (div_pos hqs hqx).le (sq_nonneg θ)).2 hr

end NTScalingProof

open Matrix

namespace NTScalingProof
open ConicQuadIPM.NTScaling
open ConicQuadIPM.Complementarity (ConeKind coord e1)

theorem quad_outer_eq (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℝ) :
    WquadOuter d w = boost (anchor .quad d) w := by
  have hwf : WellFormedBlock .quad d := by simpa [WellFormedBlock] using hd
  simp only [WquadOuter, boost, qmat_eq_signature .quad d hwf, anchor_quad]

theorem rot_outer_eq (d : ℕ) (hd : 2 ≤ d) (w : Fin d → ℝ) :
    Wrot d w = boost (anchor .rot d) w := by
  have hwf : WellFormedBlock .rot d := by simpa [WellFormedBlock] using hd
  simp only [Wrot, boost, ← anchor_dot_rot d w,
    qmat_eq_signature .rot d hwf, anchor]

theorem quad_arrow_eq (d : ℕ) (w : Fin d → ℝ) (hw : 0 < coord w 0) :
    WquadArrow w = WquadOuter d w := by
  have hden : 1 + coord w 0 ≠ 0 := by positivity
  ext i j
  by_cases hi : i.val = 0
  · have hwi : w i = coord w 0 := by rw [← hi, coord_eq]
    by_cases hj : j.val = 0
    · have hij : i = j := Fin.ext (hi.trans hj.symm)
      subst j
      simp [WquadArrow, WquadOuter, vecMulVec, Qmat, e1, e1_dot, hi, hwi]
      field_simp [hden]
      ring
    · have hij : i ≠ j := by intro h; subst j; exact hj hi
      simp [WquadArrow, WquadOuter, vecMulVec, Qmat, e1_dot, e1, hi, hj, hij, hwi]
      field_simp [hden]
  · by_cases hj : j.val = 0
    · have hwj : w j = coord w 0 := by rw [← hj, coord_eq]
      have hij : i ≠ j := by intro h; subst j; exact hi hj
      simp [WquadArrow, WquadOuter, vecMulVec, Qmat, e1_dot, e1, hi, hj, hij, hwj]
      field_simp [hden]
    · by_cases hij : i = j <;>
        simp [WquadArrow, WquadOuter, vecMulVec, Qmat, e1_dot, e1, hi, hj, hij, div_eq_mul_inv,
          mul_comm]

theorem nonneg_construct (d : ℕ) (hd : d = 1) (x s : Fin d → ℝ)
    (hx : inConeInt .nonneg x) (hs : inConeInt .nonneg s) :
    IsNT .nonneg d (thetaNT .nonneg d x s) (Wnonneg d x s) x s := by
  have hwf : WellFormedBlock .nonneg d := by simpa [WellFormedBlock] using hd
  have hn := normalization .nonneg d hwf x s hx hs
  have hsq := nonneg_theta_sq d hd x s hx hs
  have he : Real.sqrt (coord s 0 / coord x 0) = thetaNT .nonneg d x s := by
    rw [← hsq, Real.sqrt_sq hn.1.le]
  have hW : Wnonneg d x s = 1 := by
    simp [Wnonneg, he, hn.1.ne']
  rw [hW]
  apply (isNT_iff_square .nonneg d _ _ x s hn.1 ⟨PosDef.one, by simp [Qmat]⟩).2
  simp only [one_mul, one_mulVec]
  have hx0 : 0 < coord x 0 := hx
  ext i
  have hi : i.val = 0 := by omega
  have hxi : x i = coord x 0 := by rw [← hi, coord_eq]
  have hsi : s i = coord s 0 := by rw [← hi, coord_eq]
  simp only [Pi.smul_apply, smul_eq_mul, hsq, hxi, hsi]
  exact div_mul_cancel₀ _ hx0.ne'

theorem quad_construct (d : ℕ) (hd : 1 ≤ d) (x s : Fin d → ℝ)
    (hx : inConeInt .quad x) (hs : inConeInt .quad s) :
    IsNT .quad d (thetaNT .quad d x s) (WquadOuter d (wNT .quad d x s)) x s ∧
    WquadArrow (wNT .quad d x s) = WquadOuter d (wNT .quad d x s) ∧
    WquadOuter d (wNT .quad d x s) * WquadOuter d (wNT .quad d x s) =
      -Qmat .quad d + (2 : ℝ) • vecMulVec (wNT .quad d x s) (wNT .quad d x s) := by
  have hwf : WellFormedBlock .quad d := by simpa [WellFormedBlock] using hd
  have hn := normalization .quad d hwf x s hx hs
  have hw := boost_properties (anchor .quad d) (wNT .quad d x s)
    (anchor_unit .quad d hwf) (by simpa only [qmat_eq_signature .quad d hwf] using hn.2.1)
    hn.2.2.1
  have hscale : IsScaling .quad d (WquadOuter d (wNT .quad d x s)) := by
    simpa only [IsScaling, quad_outer_eq d hd, qmat_eq_signature .quad d hwf] using
      And.intro hw.1 hw.2.1
  have hsq : WquadOuter d (wNT .quad d x s) * WquadOuter d (wNT .quad d x s) =
      -Qmat .quad d + (2 : ℝ) • vecMulVec (wNT .quad d x s) (wNT .quad d x s) := by
    simpa only [quad_outer_eq d hd, qmat_eq_signature .quad d hwf] using hw.2.2
  refine ⟨(isNT_iff_square .quad d _ _ x s hn.1 hscale).2 ?_, ?_, hsq⟩
  · rw [hsq]
    exact hn.2.2.2
  · apply quad_arrow_eq
    simpa only [anchor_quad, e1_dot] using hn.2.2.1

theorem rot_construct (d : ℕ) (hd : 2 ≤ d) (x s : Fin d → ℝ)
    (hx : inConeInt .rot x) (hs : inConeInt .rot s) :
    IsNT .rot d (thetaNT .rot d x s) (Wrot d (wNT .rot d x s)) x s ∧
    Wrot d (wNT .rot d x s) * Wrot d (wNT .rot d x s) =
      -Qmat .rot d + (2 : ℝ) • vecMulVec (wNT .rot d x s) (wNT .rot d x s) := by
  have hwf : WellFormedBlock .rot d := by simpa [WellFormedBlock] using hd
  have hn := normalization .rot d hwf x s hx hs
  have hw := boost_properties (anchor .rot d) (wNT .rot d x s)
    (anchor_unit .rot d hwf) (by simpa only [qmat_eq_signature .rot d hwf] using hn.2.1)
    hn.2.2.1
  have hscale : IsScaling .rot d (Wrot d (wNT .rot d x s)) := by
    simpa only [IsScaling, rot_outer_eq d hd, qmat_eq_signature .rot d hwf] using
      And.intro hw.1 hw.2.1
  have hsq : Wrot d (wNT .rot d x s) * Wrot d (wNT .rot d x s) =
      -Qmat .rot d + (2 : ℝ) • vecMulVec (wNT .rot d x s) (wNT .rot d x s) := by
    simpa only [rot_outer_eq d hd, qmat_eq_signature .rot d hwf] using hw.2.2
  refine ⟨(isNT_iff_square .rot d _ _ x s hn.1 hscale).2 ?_, hsq⟩
  rw [hsq]
  exact hn.2.2.2

end NTScalingProof

open Matrix

namespace ConicQuadIPM.NTScaling

/-- Lemma 4.2, p. 15, for one cone block with `x, s` in the interior:
(a) every NT scaling `θ, W` satisfies (30); (b) `θ` of (30) with `W` of i) (`R₊`), (31) (`K^q`)
or (34) (`K^r`), `w` of (32), is an NT scaling; the two forms of (31) agree; and
`W² = −Q + 2wwᵀ` ((33), (35)). -/
theorem lemma_4_2 (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s) :
    (∀ (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ), IsNT kind d θ W x s →
        θ ^ 2 = Real.sqrt ((s ⬝ᵥ (Qmat kind d *ᵥ s)) / (x ⬝ᵥ (Qmat kind d *ᵥ x)))) ∧
    (kind = .nonneg →
        IsNT .nonneg d (thetaNT .nonneg d x s) (Wnonneg d x s) x s) ∧
    (kind = .quad →
        IsNT .quad d (thetaNT .quad d x s) (WquadOuter d (wNT .quad d x s)) x s ∧
        WquadArrow (wNT .quad d x s) = WquadOuter d (wNT .quad d x s) ∧
        WquadOuter d (wNT .quad d x s) * WquadOuter d (wNT .quad d x s) =
          -Qmat .quad d + (2 : ℝ) • vecMulVec (wNT .quad d x s) (wNT .quad d x s)) ∧
    (kind = .rot →
        IsNT .rot d (thetaNT .rot d x s) (Wrot d (wNT .rot d x s)) x s ∧
        Wrot d (wNT .rot d x s) * Wrot d (wNT .rot d x s) =
          -Qmat .rot d + (2 : ℝ) • vecMulVec (wNT .rot d x s) (wNT .rot d x s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ W hNT
    exact NTScalingProof.theta_necessary kind d hwf x s hx hs θ W hNT
  · intro hk
    subst kind
    exact NTScalingProof.nonneg_construct d (hwf.1 rfl) x s hx hs
  · intro hk
    subst kind
    exact NTScalingProof.quad_construct d (hwf.2.1 rfl) x s hx hs
  · intro hk
    subst kind
    exact NTScalingProof.rot_construct d (hwf.2.2 rfl) x s hx hs
end ConicQuadIPM.NTScaling

open ConicQuadIPM.NTScaling

theorem solution (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s) :
    (∀ (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ), IsNT kind d θ W x s →
        θ ^ 2 = Real.sqrt ((s ⬝ᵥ (Qmat kind d *ᵥ s)) / (x ⬝ᵥ (Qmat kind d *ᵥ x)))) ∧
    (kind = .nonneg →
        IsNT .nonneg d (thetaNT .nonneg d x s) (Wnonneg d x s) x s) ∧
    (kind = .quad →
        IsNT .quad d (thetaNT .quad d x s) (WquadOuter d (wNT .quad d x s)) x s ∧
        WquadArrow (wNT .quad d x s) = WquadOuter d (wNT .quad d x s) ∧
        WquadOuter d (wNT .quad d x s) * WquadOuter d (wNT .quad d x s) =
          -Qmat .quad d + (2 : ℝ) • vecMulVec (wNT .quad d x s) (wNT .quad d x s)) ∧
    (kind = .rot →
        IsNT .rot d (thetaNT .rot d x s) (Wrot d (wNT .rot d x s)) x s ∧
        Wrot d (wNT .rot d x s) * Wrot d (wNT .rot d x s) =
          -Qmat .rot d + (2 : ℝ) • vecMulVec (wNT .rot d x s) (wNT .rot d x s)) := by
  exact ConicQuadIPM.NTScaling.lemma_4_2 kind d hwf x s hx hs
