-- Prove2me | solution 1 for DelaunayStretch.proposition_6_7_H4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T07:41:30.540705+00:00
-- url     : https://prove2.me/submissions/b556cd81-a2bc-4544-a3ad-ce889832d117
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DelaunayStretch_prop67_central_residual
import Theorems.Thm_DelaunayStretch_prop67_outer_residual

open DelaunayStretch

namespace P67Red

theorem hstarV_rev (i j : Fin 12) (l : Fin 35) :
    hstarV (Fin.rev i) (Fin.rev j) l = -hstarV i j l := by
  have hi := i.isLt; have hj := j.isLt
  have ri : ((Fin.rev i : Fin 12) : ℕ) = 11 - i := by simp [Fin.val_rev]
  have rj : ((Fin.rev j : Fin 12) : ℕ) = 11 - j := by simp [Fin.val_rev]
  unfold hstarV
  rw [ri, rj]
  by_cases h : (i : ℕ) ≤ 5
  · rw [if_neg (show ¬ (11 - (i : ℕ) ≤ 5) by omega), if_pos h,
      show 11 - (11 - (i : ℕ)) = i by omega, show 11 - (11 - (j : ℕ)) = j by omega]
  · rw [if_pos (show 11 - (i : ℕ) ≤ 5 by omega), if_neg h, neg_neg]

theorem basisExt_eq (p : ℕ) : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
    bsplineBasisExt p j τ = bsplineBasis p j τ := by
  induction p with
  | zero => intro j τ hτ; simp [bsplineBasisExt, bsplineBasis, bsplineDeg0Ext, not_lt.mpr hτ]
  | succ p ih => intro j τ hτ; simp only [bsplineBasisExt, bsplineBasis, ih j τ hτ, ih (j+1) τ hτ]

theorem bsplineExt_eq (l : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : bsplineExt l τ = bspline l τ :=
  basisExt_eq 3 l τ hτ

theorem tau_nonneg (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ 2 * γ / Real.pi := by
  have := Real.pi_pos; positivity

theorem VExt_eq (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ a b : ℝ) (hγ : 0 ≤ γ) :
    familyVExt V γ a b = familyV V γ a b := by
  simp only [familyVExt, familyV, bsplineExt_eq _ _ (tau_nonneg γ hγ)]

theorem RExt_eq (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (γ a b : ℝ) (hγ : 0 ≤ γ) :
    familyRExt R γ a b = familyR R γ a b := by
  simp only [familyRExt, familyR, bsplineExt_eq _ _ (tau_nonneg γ hγ)]

theorem SplineExt_eq (c : Fin 35 → ℚ) (γ : ℝ) (hγ : 0 ≤ γ) :
    familySplineExt c γ = familySpline c γ := by
  simp only [familySplineExt, familySpline, bsplineExt_eq _ _ (tau_nonneg γ hγ)]

theorem bernstein_one_sub (d i : ℕ) (hi : i ≤ d) (x : ℝ) :
    DelaunayStretch.bernstein d i (1 - x) = DelaunayStretch.bernstein d (d - i) x := by
  unfold DelaunayStretch.bernstein
  rw [Nat.choose_symm hi, Nat.sub_sub_self hi]; ring

theorem familyVExt_reflect (V : Fin 12 → Fin 12 → Fin 35 → ℚ)
    (hV : ∀ i j l, V (Fin.rev i) (Fin.rev j) l = -V i j l) (γ a b : ℝ) :
    familyVExt V γ (1 - a) (1 - b) = -familyVExt V γ a b := by
  unfold familyVExt
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro l _
  simp only [Fin.revPerm_apply]
  rw [bernstein_one_sub 11 _ (by omega), bernstein_one_sub 11 _ (by omega), hV]
  simp only [Fin.val_rev, Rat.cast_neg]
  have e1 : 11 - (12 - ((i : ℕ) + 1)) = i := by omega
  have e2 : 11 - (12 - ((j : ℕ) + 1)) = j := by omega
  rw [e1, e2]; ring

theorem omega_facts (γ φ θ : ℝ) (h : (γ, φ, θ) ∈ OmegaSet) :
    |γ| < Real.pi / 2 ∧ 0 ≤ (θ - φ + γ) / (Real.pi + 2 * γ) ∧
      (θ - φ + γ) / (Real.pi + 2 * γ) ≤ 1 ∧
      0 ≤ (θ + φ - γ) / (Real.pi - 2 * γ) ∧ (θ + φ - γ) / (Real.pi - 2 * γ) ≤ 1 := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hb1 := le_abs_self (γ - φ); have hb2 := neg_abs_le (γ - φ)
  have hc1 := le_abs_self (γ + φ); have hc2 := neg_abs_le (γ + φ)
  have hg : |γ| < Real.pi / 2 := by
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨g1, g2⟩ := abs_lt.mp hg
  have p1 : 0 < Real.pi + 2 * γ := by linarith
  have p2 : 0 < Real.pi - 2 * γ := by linarith
  refine ⟨hg, ?_, ?_, ?_, ?_⟩
  · apply div_nonneg _ p1.le; linarith
  · rw [div_le_one p1]; linarith
  · apply div_nonneg _ p2.le; linarith
  · rw [div_le_one p2]; linarith

/-- For `γ ≥ 0`, `H⋆` is `Ĥ` evaluated at the clipped balance variable. -/
theorem Hstar_eq (z : R4) (hγ : 0 ≤ z.1) :
    Hstar z = familyHhat hstarV hstarR hstarB hstarD z.1 (posA z) (posB z)
      (clip 1 (balanceXi z)) := by
  simp only [familyHhat, VExt_eq _ _ _ _ hγ, RExt_eq _ _ _ _ hγ, SplineExt_eq _ _ hγ]
  simp only [Hstar, familyH, if_pos hγ, familyHPos, posA, posB, balanceXi]

theorem clip_of_abs (x : ℝ) (h : |x| ≤ 1) : clip 1 x = x := by
  unfold clip; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

theorem clip_of_ge (x : ℝ) (h : 1 ≤ x) : clip 1 x = 1 := by
  unfold clip; rw [min_eq_left h, max_eq_right (by norm_num)]

theorem clip_of_le (x : ℝ) (h : x ≤ -1) : clip 1 x = -1 := by
  unfold clip; rw [min_eq_right (by linarith), max_eq_left h]

theorem res_congr (U : ℝ) (H H' : R4 → ℝ) (g z : R4) (h : H z = H' z) :
    pencilResidual U H g z = pencilResidual U H' g z := by
  unfold pencilResidual; rw [h]

theorem coord_inv (z : R4) (hγ : |z.1| < Real.pi / 2) :
    coordPt z.1 (posA z) (posB z) (balanceXi z) = z := by
  obtain ⟨g1, g2⟩ := abs_lt.mp hγ
  have p1 : Real.pi + 2 * z.1 ≠ 0 := by linarith
  have p2 : Real.pi - 2 * z.1 ≠ 0 := by linarith
  have hk : Real.pi / 2 - Real.cos z.1 ≠ 0 := by
    have := Real.cos_le_one z.1; have := Real.pi_gt_three; linarith
  have e1 : ∀ x : ℝ, (Real.pi / 2 + z.1) * (x / (Real.pi + 2 * z.1)) = x / 2 := fun x => by
    rw [mul_div_assoc', div_eq_div_iff p1 two_ne_zero]; ring
  have e2 : ∀ x : ℝ, (Real.pi / 2 - z.1) * (x / (Real.pi - 2 * z.1)) = x / 2 := fun x => by
    rw [mul_div_assoc', div_eq_div_iff p2 two_ne_zero]; ring
  have e3 : (Real.pi / 2 - Real.cos z.1) * (z.2.2.2 / (Real.pi / 2 - Real.cos z.1)) = z.2.2.2 := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hk]
  simp only [coordPt, posA, posB, balanceXi]
  rw [e1, e2, e3]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> simp only <;> ring

theorem hout_shift (s : ℝ) (w : R4) (t : ℝ) :
    pieceHout hstarV hstarR hstarB hstarD s (w + (0, 0, 0, t)) =
      pieceHout hstarV hstarR hstarB hstarD s w := by
  obtain ⟨γ, φ, θ, ψ⟩ := w
  simp [pieceHout, posA, posB]

theorem fderiv_shift (F : R4 → ℝ) (hF : ∀ w t, F (w + (0, 0, 0, t)) = F w) (z : R4) (t : ℝ) :
    fderiv ℝ F (z + (0, 0, 0, t)) = fderiv ℝ F z := by
  rw [← fderiv_comp_add_right (f := F) (x := z) ((0, 0, 0, t) : R4)]
  congr 1; funext w; exact hF w t

theorem dpsi_zero (F : R4 → ℝ) (hF : ∀ w t, F (w + (0, 0, 0, t)) = F w) (z : R4) :
    fderiv ℝ F z (0, 0, 0, 1) = 0 := by
  by_cases hd : DifferentiableAt ℝ F z
  · have h1 : HasDerivAt (fun t : ℝ => z + t • ((0, 0, 0, 1) : R4)) ((0, 0, 0, 1) : R4) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const ((0, 0, 0, 1) : R4)).const_add z
    have h2 : HasDerivAt (fun t : ℝ => F (z + t • ((0, 0, 0, 1) : R4)))
        (fderiv ℝ F z (0, 0, 0, 1)) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hd.hasFDerivAt h1 (by simp)
    have hc : (fun t : ℝ => F (z + t • ((0, 0, 0, 1) : R4))) = fun _ => F z := by
      funext t
      have : t • ((0, 0, 0, 1) : R4) = (0, 0, 0, t) := by simp
      rw [this, hF]
    rw [hc] at h2
    exact h2.unique (hasDerivAt_const 0 (F z))
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

/-- The linear part of the reflection `ρ₂`. -/
noncomputable def Lr : R4 ≃L[ℝ] R4 :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr ((ContinuousLinearEquiv.neg ℝ).prodCongr
    ((ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)))

theorem Lr_apply (w : R4) : Lr w = (w.1, -w.2.1, -w.2.2.1, -w.2.2.2) := by
  simp [Lr]

/-- The reflection `ρ₂(γ, φ, θ, ψ) = (γ, −φ, π − θ, −ψ)`. -/
noncomputable def rho2 (w : R4) : R4 := (w.1, -w.2.1, Real.pi - w.2.2.1, -w.2.2.2)

theorem rho2_eq (w : R4) : rho2 w = Lr w + (0, 0, Real.pi, 0) := by
  rw [Lr_apply]; simp only [rho2, Prod.mk_add_mk, add_zero]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl)); simp only; ring

theorem fderiv_refl (F G : R4 → ℝ) (z : R4) (h : F =ᶠ[nhds z] fun w => -G (rho2 w)) :
    fderiv ℝ F z = -(fderiv ℝ G (rho2 z)).comp (Lr : R4 →L[ℝ] R4) := by
  rw [h.fderiv_eq, fderiv_fun_neg]
  have : (fun w => G (rho2 w)) = (fun u => G (u + ((0, 0, Real.pi, 0) : R4))) ∘ Lr := by
    funext w; simp [rho2_eq]
  rw [this, ContinuousLinearEquiv.comp_right_fderiv, fderiv_comp_add_right, ← rho2_eq]

theorem grad_refl (F G : R4 → ℝ) (z : R4) (h : F =ᶠ[nhds z] fun w => -G (rho2 w)) :
    (gradient4 F z).1 = -(gradient4 G (rho2 z)).1 ∧
      (gradient4 F z).2.2.1 = (gradient4 G (rho2 z)).2.2.1 := by
  simp only [gradient4, fderiv_refl F G z h, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Lr_apply]
  constructor
  · simp
  · have e : ((0:ℝ), -(0:ℝ), -(1:ℝ), -(0:ℝ)) = -((0, 0, 1, 0) : R4) := by simp
    simp only [e, map_neg, neg_neg]

theorem hout_refl_ev (z : R4) (hz : |z.1| < Real.pi / 2) :
    pieceHout hstarV hstarR hstarB hstarD (-1) =ᶠ[nhds z]
      fun w => -pieceHout hstarV hstarR hstarB hstarD 1 (rho2 w) := by
  have hopen : IsOpen {w : R4 | |w.1| < Real.pi / 2} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hw' : |w.1| < Real.pi / 2 := hw
  obtain ⟨g1, g2⟩ := abs_lt.mp hw'
  have p1 : Real.pi + 2 * w.1 ≠ 0 := by linarith
  have p2 : Real.pi - 2 * w.1 ≠ 0 := by linarith
  have ea : posA (rho2 w) = 1 - posA w := by
    simp only [posA, rho2]
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq p1]; ring
  have eb : posB (rho2 w) = 1 - posB w := by
    simp only [posB, rho2]
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq p2]; ring
  have rγ : (rho2 w).1 = w.1 := rfl
  simp only [pieceHout]
  rw [ea, eb, rγ]
  simp only [familyHhat, familyVExt_reflect hstarV hstarV_rev]
  ring

theorem res_refl (U : ℝ) (z : R4) (hz : |z.1| < Real.pi / 2) :
    pencilResidual U (pieceHout hstarV hstarR hstarB hstarD (-1))
        (gradient4 (pieceHout hstarV hstarR hstarB hstarD (-1)) z) z =
      pencilResidual U (pieceHout hstarV hstarR hstarB hstarD 1)
        (gradient4 (pieceHout hstarV hstarR hstarB hstarD 1) (rho2 z)) (rho2 z) := by
  have hev := hout_refl_ev z hz
  obtain ⟨g1, g3⟩ := grad_refl _ _ z hev
  have hv : pieceHout hstarV hstarR hstarB hstarD (-1) z =
      -pieceHout hstarV hstarR hstarB hstarD 1 (rho2 z) := hev.eq_of_nhds
  have d1 : (gradient4 (pieceHout hstarV hstarR hstarB hstarD (-1)) z).2.2.2 = 0 :=
    dpsi_zero _ (hout_shift (-1)) z
  have d2 : (gradient4 (pieceHout hstarV hstarR hstarB hstarD 1) (rho2 z)).2.2.2 = 0 :=
    dpsi_zero _ (hout_shift 1) _
  unfold pencilResidual pencilA
  rw [hv, g1, g3, d1, d2]
  simp only [rho2, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_neg, Real.sin_neg]
  ring

theorem res_out_shift (U s γ a b ξ : ℝ) :
    pencilResidual U (pieceHout hstarV hstarR hstarB hstarD s)
        (gradient4 (pieceHout hstarV hstarR hstarB hstarD s) (coordPt γ a b ξ))
        (coordPt γ a b ξ) = resOut U s γ a b := by
  have e : coordPt γ a b ξ = coordPt γ a b s +
      (0, 0, 0, (Real.pi / 2 - Real.cos γ) * ξ - (Real.pi / 2 - Real.cos γ) * s) := by
    simp only [coordPt, Prod.mk_add_mk, add_zero]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)); simp only; ring
  have hv : pieceHout hstarV hstarR hstarB hstarD s (coordPt γ a b ξ) =
      pieceHout hstarV hstarR hstarB hstarD s (coordPt γ a b s) := by
    rw [e, hout_shift]
  have hg : gradient4 (pieceHout hstarV hstarR hstarB hstarD s) (coordPt γ a b ξ) =
      gradient4 (pieceHout hstarV hstarR hstarB hstarD s) (coordPt γ a b s) := by
    unfold gradient4; rw [e, fderiv_shift _ (hout_shift s)]
  have d : (gradient4 (pieceHout hstarV hstarR hstarB hstarD s) (coordPt γ a b s)).2.2.2 = 0 :=
    dpsi_zero _ (hout_shift s) _
  unfold resOut pencilResidual pencilA
  rw [hv, hg, d]
  simp only [coordPt, mul_zero]

theorem rho2_coord (γ a b ξ : ℝ) :
    rho2 (coordPt γ a b ξ) = coordPt γ (1 - a) (1 - b) (-ξ) := by
  simp only [rho2, coordPt]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

theorem solution :
    ∀ z ∈ SigmaSet, ∀ g : R4, IsPieceGradient hstarV hstarR hstarB hstarD z g →
      pencilResidual (159485994 / 100000000 : ℝ) Hstar g z ≤ 0 := by
  intro z hz g hg
  obtain ⟨hzO, hγ, hcase⟩ := hg
  obtain ⟨-, hacc⟩ := hz
  obtain ⟨hγb, ha0, ha1, hb0, hb1⟩ := omega_facts z.1 z.2.1 z.2.2.1 hzO
  have ha0' : 0 ≤ posA z := ha0
  have ha1' : posA z ≤ 1 := ha1
  have hb0' : 0 ≤ posB z := hb0
  have hb1' : posB z ≤ 1 := hb1
  have hγ2 : z.1 < Real.pi / 2 := (abs_lt.mp hγb).2
  have hci := coord_inv z hγb
  have hacc' : Accessible z.1 (posA z) (posB z) (balanceXi z) := by
    have : |(coordPt z.1 (posA z) (posB z) (balanceXi z)).2.2.2 -
        (coordPt z.1 (posA z) (posB z) (balanceXi z)).2.1| ≤
        Real.sin (coordPt z.1 (posA z) (posB z) (balanceXi z)).2.2.1 := by
      rw [hci]; exact hacc
    exact this
  rcases hcase with ⟨hξ, rfl⟩ | ⟨hξ, rfl⟩ | ⟨hξ, rfl⟩
  · rw [res_congr _ _ (pieceHc hstarV hstarR hstarB hstarD) _ _
      (by rw [Hstar_eq z hγ, clip_of_abs _ hξ]; try rfl)]
    have := prop67_central_residual z.1 (posA z) (posB z) (balanceXi z) hγ hγ2 ha0' ha1' hb0'
      hb1' hξ hacc'
    unfold resC at this; rw [hci] at this; exact this
  · rw [res_congr _ _ (pieceHout hstarV hstarR hstarB hstarD 1) _ _
      (by rw [Hstar_eq z hγ, clip_of_ge _ hξ]; try rfl)]
    have := prop67_outer_residual z.1 (posA z) (posB z) (balanceXi z) hγ hγ2 ha0' ha1' hb0'
      hb1' hξ hacc'
    rw [← res_out_shift _ _ _ _ _ (balanceXi z), hci] at this; exact this
  · rw [res_congr _ _ (pieceHout hstarV hstarR hstarB hstarD (-1)) _ _
      (by rw [Hstar_eq z hγ, clip_of_le _ hξ]; try rfl)]
    rw [res_refl _ z hγb]
    have hr : rho2 z = coordPt z.1 (1 - posA z) (1 - posB z) (-balanceXi z) := by
      rw [← rho2_coord, hci]
    have hacc2 : Accessible z.1 (1 - posA z) (1 - posB z) (-balanceXi z) := by
      have : |(coordPt z.1 (1 - posA z) (1 - posB z) (-balanceXi z)).2.2.2 -
          (coordPt z.1 (1 - posA z) (1 - posB z) (-balanceXi z)).2.1| ≤
          Real.sin (coordPt z.1 (1 - posA z) (1 - posB z) (-balanceXi z)).2.2.1 := by
        rw [← hr]; simp only [rho2]
        rw [Real.sin_pi_sub, show -z.2.2.2 - -z.2.1 = -(z.2.2.2 - z.2.1) by ring, abs_neg]
        exact hacc
      exact this
    have := prop67_outer_residual z.1 (1 - posA z) (1 - posB z) (-balanceXi z) hγ hγ2
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hacc2
    rw [← res_out_shift _ _ _ _ _ (-balanceXi z), ← hr] at this; exact this

end P67Red

theorem solution :
    ∀ z ∈ DelaunayStretch.SigmaSet, ∀ g : DelaunayStretch.R4,
      DelaunayStretch.IsPieceGradient DelaunayStretch.hstarV DelaunayStretch.hstarR
        DelaunayStretch.hstarB DelaunayStretch.hstarD z g →
      DelaunayStretch.pencilResidual (159485994 / 100000000 : ℝ) DelaunayStretch.Hstar g z ≤ 0 :=
  P67Red.solution
