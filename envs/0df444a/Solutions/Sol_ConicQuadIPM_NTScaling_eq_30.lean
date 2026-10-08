-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:56:20.740813+00:00
-- url     : https://prove2.me/submissions/5b681a1b-2431-4d92-a575-7b2b965a6763

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix ConicQuadIPM.Complementarity
set_option maxRecDepth 4000
private lemma comp_qsq (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) : Qmat c d * Qmat c d = 1 := by
  cases c
  · simp [Qmat]
  · simp only [Qmat, diagonal_mul_diagonal]
    ext a b
    by_cases h : a.val = 0 <;> simp [h, diagonal_apply, one_apply]
  · have hd := hwf.2.2 rfl
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    ext a b
    change (∑ j : Fin d, Qmat .rot d a j * Qmat .rot d j b) = if a = b then 1 else 0
    simp only [Qmat]
    by_cases ha : a.val < 2
    · have ha' : a = z ∨ a = o := by dsimp [z, o]; rcases (by omega : a.val = 0 ∨ a.val = 1) with h | h <;> [left; right] <;> apply Fin.ext <;> exact h
      rcases ha' with rfl | rfl
      · rw [Finset.sum_eq_single o]
        · by_cases hb : b = z <;> simp_all [z, o, Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega
        · intro j hj hjo
          have : j.val ≠ 1 := by intro h; apply hjo; apply Fin.ext; exact h
          simp [z, o, this]; split_ifs <;> simp_all <;> omega
        · simp
      · rw [Finset.sum_eq_single z]
        · by_cases hb : b = o <;> simp_all [z, o, Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega
        · intro j hj hjz
          have : j.val ≠ 0 := by intro h; apply hjz; apply Fin.ext; exact h
          simp [z, o, this]; split_ifs <;> simp_all <;> omega
        · simp
    · rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro j hj hja; simp [ha, Ne.symm hja]
      · simp


private lemma qmatch (c : ConeKind) (d : ℕ) :
    ConicQuadIPM.NTScaling.Qmat c d = Qmat c d := by
  cases c
  · rfl
  · ext a b
    simp [ConicQuadIPM.NTScaling.Qmat, Qmat, diagonal_apply]
  · ext a b
    change (if (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) then (1 : ℝ)
      else if a = b ∧ 2 ≤ a.val then -1 else 0) =
      (if a.val < 2 ∧ b.val < 2 then (if a.val ≠ b.val then 1 else 0) else if a = b then -1 else 0)
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega


private lemma transport {d : ℕ} (M Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    (M *ᵥ x) ⬝ᵥ (Q *ᵥ (M *ᵥ x)) = x ⬝ᵥ ((Mᵀ * Q * M) *ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

open ConicQuadIPM.NTScaling in
private theorem scaling_identities (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (θ : ℝ) (hθ : 0 < θ) (W : Matrix (Fin d) (Fin d) ℝ) (hW : IsScaling kind d W)
    (x s : Fin d → ℝ) :
    x ⬝ᵥ s = xbar θ W x ⬝ᵥ sbar θ W s ∧
    θ ^ 2 * (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x)) = xbar θ W x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ xbar θ W x) ∧
    (θ ^ 2)⁻¹ * (s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s)) = sbar θ W s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ sbar θ W s) := by
  let Q := ConicQuadIPM.NTScaling.Qmat kind d
  have hQ : Q * Q = 1 := by
    dsimp [Q]; rw [qmatch]; exact comp_qsq kind d hwf
  have hsc : W * Q * W = Q := hW.2
  have hsym : Wᵀ = W := by
    ext a b
    simpa using hW.1.isHermitian.apply a b
  have hi : (θ • W)⁻¹ = θ⁻¹ • (Q * W * Q) := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
    calc
      W * (Q * W * Q) = (W * Q * W) * Q := by noncomm_ring
      _ = 1 := by rw [hsc, hQ]
  have hQi : Qᵀ = Q := by
    dsimp [Q]
    rw [qmatch]
    cases kind
    · simp [ConicQuadIPM.Complementarity.Qmat]
    · simp [ConicQuadIPM.Complementarity.Qmat]
    · ext a b
      change ConicQuadIPM.Complementarity.Qmat .rot d b a = ConicQuadIPM.Complementarity.Qmat .rot d a b
      simp [ConicQuadIPM.Complementarity.Qmat, and_comm, eq_comm]
  have hsymi : (Q * W * Q)ᵀ = Q * W * Q := by
    rw [transpose_mul, transpose_mul, hQi, hsym]
    noncomm_ring
  have hpresi : (Q * W * Q)ᵀ * Q * (Q * W * Q) = Q := by
    rw [hsymi]
    calc
      (Q * W * Q) * Q * (Q * W * Q) = Q * (W * Q * W) * Q := by
        calc
          _ = Q * W * (Q * Q) * Q * W * Q := by noncomm_ring
          _ = Q * (W * Q * W) * Q := by rw [hQ]; simp [mul_assoc]
      _ = Q := by rw [hsc, hQ, one_mul]
  have hprod : (θ • W)ᵀ * (θ • W)⁻¹ = 1 := by
    rw [transpose_smul, hsym, hi, smul_mul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
    calc
      W * (Q * W * Q) = (W * Q * W) * Q := by noncomm_ring
      _ = 1 := by rw [hsc, hQ]
  refine ⟨?_, ?_, ?_⟩
  · unfold xbar sbar
    rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec, hprod, one_mulVec]
  · unfold xbar
    rw [smul_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul, transport, hsym, hsc]
    simp only [smul_eq_mul]
    ring
  · unfold sbar
    rw [hi, smul_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul, transport, hpresi]
    simp only [smul_eq_mul, inv_pow]
    ring


private lemma coordinate {d : ℕ} (v : Fin d → ℝ) (r : ℕ) (hr : r < d) : coord v r = v ⟨r, hr⟩ := by
  unfold coord
  rw [Finset.sum_eq_single ⟨r, hr⟩]
  · simp
  · intro j hj h; simp [show j.val ≠ r by intro he; apply h; exact Fin.ext he]
  · simp

private lemma qrot_action (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) (a : Fin d) :
    (Qmat .rot d *ᵥ v) a = if a.val = 0 then coord v 1 else if a.val = 1 then coord v 0 else -v a := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change (∑ j : Fin d, Qmat .rot d a j * v j) = _
  by_cases h0 : a.val = 0
  · rw [Finset.sum_eq_single o]
    · simp [Qmat, h0, z, o, coordinate v 1 (by omega)]
    · intro j hj hjo
      have hn : j.val ≠ 1 := by intro he; apply hjo; exact Fin.ext he
      simp [Qmat, h0, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · simp
  · by_cases h1 : a.val = 1
    · rw [Finset.sum_eq_single z]
      · simp [Qmat, h1, z, o, coordinate v 0 (by omega)]
      · intro j hj hjz
        have hn : j.val ≠ 0 := by intro he; apply hjz; exact Fin.ext he
        simp [Qmat, h1, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      · simp
    · rw [Finset.sum_eq_single a]
      · simp [Qmat, h0, h1, show ¬ a.val < 2 by omega]
      · intro j hj hja
        simp [Qmat, show ¬ a.val < 2 by omega, Ne.symm hja]
      · simp

private lemma quad_form (d : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .quad d *ᵥ v) = coord v 0 ^ 2 - tailSq v 1 := by
  have hhead : (∑ j : Fin d, if j.val = 0 then v j ^ 2 else 0) = coord v 0 ^ 2 := by
    cases d with
    | zero => simp [coord]
    | succ d =>
      rw [coordinate v 0 (by omega), Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj h; simp [show j.val ≠ 0 by intro he; apply h; exact Fin.ext he]
      · simp
  change (∑ j : Fin d, v j * (Qmat .quad d *ᵥ v) j) = _
  have he : ∀ j : Fin d, v j * (Qmat .quad d *ᵥ v) j =
      (if j.val = 0 then v j ^ 2 else 0) - (if 1 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    simp only [Qmat, Matrix.mulVec_diagonal]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  rw [hhead]; rfl

private lemma rot_form (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .rot d *ᵥ v) = 2 * coord v 0 * coord v 1 - tailSq v 2 := by
  have he : ∀ j : Fin d, v j * (Qmat .rot d *ᵥ v) j =
      (if j = (⟨0, by omega⟩ : Fin d) then v j * coord v 1 else 0) +
      (if j = (⟨1, by omega⟩ : Fin d) then v j * coord v 0 else 0) -
      (if 2 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    rw [qrot_action d hd]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  change (∑ j : Fin d, v j * (Qmat .rot d *ᵥ v) j) = _
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← coordinate v 0 (by omega), ← coordinate v 1 (by omega)]
  unfold tailSq; ring

private lemma int_form (c : ConeKind) (d : ℕ) (hw : ConicQuadIPM.NTScaling.WellFormedBlock c d)
    (v : Fin d → ℝ) (hv : ConicQuadIPM.NTScaling.inConeInt c v) :
    0 < v ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat c d *ᵥ v) := by
  rw [qmatch]
  cases c
  · have hd := hw.1 rfl
    subst d
    simpa [Qmat, dotProduct, coord, ConicQuadIPM.NTScaling.inConeInt,
      ConicQuadIPM.NTScaling.inNonnegInt] using mul_pos hv hv
  · rw [quad_form]
    exact sub_pos.mpr hv.1
  · rw [rot_form d (hw.2.2 rfl)]
    exact sub_pos.mpr hv.1

open ConicQuadIPM.NTScaling in
theorem solution (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s)
    (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) (hNT : IsNT kind d θ W x s) :
    θ ^ 2 = Real.sqrt ((s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s)) / (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x))) := by
  obtain ⟨hθ, hW, heq⟩ := hNT
  obtain ⟨_, hxid, hsid⟩ := scaling_identities kind d hwf θ hθ W hW x s
  have hsame : xbar θ W x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ xbar θ W x) =
      sbar θ W s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ sbar θ W s) := by rw [heq]
  have hp := int_form kind d hwf x hx
  have hθ2 : θ ^ 2 ≠ 0 := pow_ne_zero 2 hθ.ne'
  have hid : (θ ^ 2)^2 * (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x)) =
      s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s) := by
    have hh : θ ^ 2 * (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x)) =
        (θ ^ 2)⁻¹ * (s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s)) := hxid.trans (hsame.trans hsid.symm)
    calc
      (θ ^ 2)^2 * (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x)) =
          θ^2 * (θ^2 * (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x))) := by ring
      _ = θ^2 * ((θ^2)⁻¹ * (s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s))) := by rw [hh]
      _ = s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s) := by
        rw [← mul_assoc, mul_inv_cancel₀ hθ2, one_mul]
  have hr : (s ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ s)) /
      (x ⬝ᵥ (ConicQuadIPM.NTScaling.Qmat kind d *ᵥ x)) = (θ^2)^2 := by
    rw [← hid, mul_div_cancel_right₀ _ hp.ne']
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg θ)]

#print axioms solution
