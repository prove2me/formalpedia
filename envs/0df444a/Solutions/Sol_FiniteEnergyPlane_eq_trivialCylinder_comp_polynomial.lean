-- Prove2me | solution 1 for FiniteEnergyPlane.eq_trivialCylinder_comp_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:43:42.871644+00:00
-- url     : https://prove2.me/submissions/55daeffd-ecc2-4bf1-8686-ee31eef0b6e1

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn

set_option linter.all false

-- ===== DP_a =====
section S_DP_a


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

/-- partner index -/
def pt (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

lemma j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

lemma j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := j0_add, map_smul' := j0_smul }

@[simp] lemma j0L_apply (u : V n) : j0L u = j0 u := rfl

lemma dot_j0_anti (u v : V n) : dot (j0 u) v = - dot (j0 v) u := by
  rw [eq_neg_iff_add_eq_zero, dot, dot, ← Finset.sum_add_distrib]
  refine Finset.sum_involution (fun k _ => pt k) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro k _
    simp only [pt, j0]
    by_cases hk : (k : ℕ) % 2 = 0
    · have h1 : ((k : ℕ) + 1) % 2 ≠ 0 := by omega
      simp only [hk, h1, ↓reduceIte, ↓reduceDIte]
      have : (⟨(k:ℕ) + 1 - 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
        ext; simp
      rw [this]; ring
    · have h1 : ((k : ℕ) - 1) % 2 = 0 := by omega
      simp only [hk, h1, ↓reduceIte, ↓reduceDIte]
      have : (⟨(k:ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
        ext; simp; omega
      rw [this]; ring
  · intro k _ _ h
    simp only [pt] at h; split_ifs at h with hk <;> simp only [Fin.ext_iff] at h <;> omega
  · intro k _
    by_cases hk : (k : ℕ) % 2 = 0
    · have h1 : ((k : ℕ) + 1) % 2 ≠ 0 := by omega
      simp only [pt, hk, h1, ↓reduceDIte, Fin.ext_iff]; omega
    · have h1 : ((k : ℕ) - 1) % 2 = 0 := by omega
      simp only [pt, hk, h1, ↓reduceDIte, Fin.ext_iff]; omega

lemma omega0_anti (u v : V n) : omega0 u v = - omega0 v u := dot_j0_anti u v

lemma omega0_self (u : V n) : omega0 u u = 0 := by
  have := omega0_anti u u; linarith

lemma omega0_add_left (u u' v : V n) : omega0 (u + u') v = omega0 u v + omega0 u' v := by
  simp [omega0, dot, j0_add, add_mul, Finset.sum_add_distrib]

lemma omega0_smul_left (c : ℝ) (u v : V n) : omega0 (c • u) v = c * omega0 u v := by
  simp [omega0, dot, j0_smul, Finset.mul_sum, mul_assoc]

lemma omega0_add_right (u v v' : V n) : omega0 u (v + v') = omega0 u v + omega0 u v' := by
  simp [omega0, dot, mul_add, Finset.sum_add_distrib]

lemma omega0_smul_right (c : ℝ) (u v : V n) : omega0 u (c • v) = c * omega0 u v := by
  simp [omega0, dot, Finset.mul_sum]; congr 1; funext k; ring

lemma omega0_sub_right (u v v' : V n) : omega0 u (v - v') = omega0 u v - omega0 u v' := by
  rw [sub_eq_add_neg, omega0_add_right, show -v' = (-1:ℝ) • v' by simp, omega0_smul_right]; ring

lemma liouvilleCLM_apply (x v : V n) : liouvilleCLM x v = liouville x v := by
  simp [liouvilleCLM, liouville, omega0, dot]
  ring

lemma scaleToS_pos (H : V n → ℝ) (y : V n) : 0 < scaleToS H y := by
  unfold scaleToS; split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact one_pos

lemma proj_eq (H : V n → ℝ) (y : V n) : proj H y = scaleToS H y • y := rfl

lemma exp_aCoord (H : V n → ℝ) (y : V n) : Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
  rw [aCoord, show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
    Real.exp_neg, Real.exp_log (scaleToS_pos H y)]

end DP

end S_DP_a

-- ===== DP_b =====
section S_DP_b


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

/-- Algebra of `J̃` at `y ≠ 0` with `x = proj y ∈ S`. -/
lemma jtilde_AL (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (y : V n)
    (hx : H (proj H y) = 1) (v : V n) :
    fderiv ℝ H (proj H y) (Jtilde H J y v) =
        -(scaleToS H y * liouvilleCLM (proj H y) v) * (2 * fderiv ℝ H (proj H y) y) ∧
      liouvilleCLM (proj H y) (Jtilde H J y v) =
        (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) * fderiv ℝ H (proj H y) v) *
          (scaleToS H y)⁻¹ := by
  set x := proj H y with hxdef
  set r := scaleToS H y with hrdef
  have hr : 0 < r := scaleToS_pos H y
  have hxS : x ∈ energySurface H := hx
  obtain ⟨-, hLR, hAR, -⟩ := reeb_spec H hH x hxS
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hyx : y = r⁻¹ • x := by rw [hxdef, proj_eq, ← hrdef, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hLy : liouvilleCLM x y = 0 := by
    rw [liouvilleCLM_apply, liouville, hyx, omega0_smul_right, omega0_self]; simp
  have hAy : fderiv ℝ H x y = r⁻¹ * fderiv ℝ H x x := by rw [hyx, map_smul, smul_eq_mul]
  set α : ℝ := r / (2 * (fderiv ℝ H x) x) * (fderiv ℝ H x) v
  set β : ℝ := r * (liouvilleCLM x) v
  set ζ : V n := v - α • ((2:ℝ) • y) - β • (r⁻¹ • reeb H x)
  have hLR' : (liouvilleCLM x) (reeb H x) = 1 := by rw [liouvilleCLM_apply]; exact hLR
  have hζ : IsInXi H x ζ := by
    constructor
    · rw [← liouvilleCLM_apply]
      simp only [ζ, map_sub, map_smul, smul_eq_mul, hLy, hLR']
      field_simp; ring
    · simp only [ζ, map_sub, map_smul, smul_eq_mul, hAR, hAy, α]
      field_simp; ring
  have hJζ := (hJ.2 x hxS ζ ζ hζ hζ).1
  have hJt : Jtilde H J y v = α • (r⁻¹ • reeb H x) - β • ((2:ℝ) • y) + J x ζ := by
    simp only [Jtilde, ← hxdef, ← hrdef, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  have hLJ : (liouvilleCLM x) (J x ζ) = 0 := by rw [liouvilleCLM_apply]; exact hJζ.1
  constructor
  · rw [hJt]; simp only [map_add, map_sub, map_smul, smul_eq_mul, hAR, hJζ.2, β, hAy]; ring
  · rw [hJt]; simp only [map_add, map_sub, map_smul, smul_eq_mul, hLR', hLy, hLJ, α]; ring

end DP

end S_DP_b

-- ===== DP_c =====
section S_DP_c


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

lemma smooth_aw (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) :
    ContDiff ℝ ∞ (fun z => aCoord H (u z)) ∧ ContDiff ℝ ∞ (fun z => proj H (u z)) := by
  obtain ⟨-, hP, hAc, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  exact ⟨hAc.comp_contDiff hsm hu0, hP.comp_contDiff hsm hu0⟩

lemma fderiv_u (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (z v : ℂ) :
    fderiv ℝ u z v = (Real.exp (2 * aCoord H (u z)) * (2 * fderiv ℝ (fun z => aCoord H (u z)) z v)) •
        proj H (u z) + Real.exp (2 * aCoord H (u z)) • fderiv ℝ (fun z => proj H (u z)) z v := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ u hsm hu0
  have hueq : u = fun z => Real.exp (2 * aCoord H (u z)) • proj H (u z) :=
    funext fun z => (hrel _ (hu0 z)).2
  have hA := (ha.differentiable (by simp) z).hasFDerivAt
  have hW := (hw.differentiable (by simp) z).hasFDerivAt
  have hE := (hA.const_mul 2).exp
  have hD := hE.smul hW
  have hD' : HasFDerivAt u _ z :=
    hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => congrFun hueq w)
  rw [hD'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  abel

lemma dH_w (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (z v : ℂ) :
    fderiv ℝ H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z v) = 0 := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨-, hw⟩ := smooth_aw H hH J hJ u hsm hu0
  have hW := (hw.differentiable (by simp) z).hasFDerivAt
  have hc := (hH.1.differentiable (by simp) (proj H (u z))).hasFDerivAt.comp z hW
  have hconst : (fun z => H (proj H (u z))) = fun _ => (1:ℝ) := funext fun z => (hrel _ (hu0 z)).1
  have h2 : HasFDerivAt (fun z => H (proj H (u z))) (0 : ℂ →L[ℝ] ℝ) z := by
    rw [hconst]; exact hasFDerivAt_const _ _
  have := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hc.unique h2)
  simpa using this

theorem cr_rel (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hsm : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) univ u) (z : ℂ) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
      dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hdb := (hhol z (mem_univ z)).2
  simp only [JHolomorphic.dbarJ] at hdb
  have hx : H (proj H (u z)) = 1 := (hrel _ (hu0 z)).1
  have hyeq : u z = Real.exp (2 * aCoord H (u z)) • proj H (u z) := (hrel _ (hu0 z)).2
  obtain ⟨hJA, hJL⟩ := jtilde_AL H hH J hJ (u z) hx (fderiv ℝ u z Complex.I)
  have hfu := fderiv_u H hH J hJ u hsm hu0 z
  have hAw := dH_w H hH J hJ u hsm hu0 z
  set y := u z with hy
  set x := proj H y with hxdef
  set e := Real.exp (2 * aCoord H y) with he
  set r := scaleToS H y with hr
  have hre : r * e = 1 := by rw [he, exp_aCoord, ← hr, mul_inv_cancel₀ (scaleToS_pos H y).ne']
  have hrpos : 0 < r := scaleToS_pos H y
  have hepos : 0 < e := Real.exp_pos _
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hLx : liouvilleCLM x x = 0 := by rw [liouvilleCLM_apply, liouville, omega0_self]; simp
  have hAy : fderiv ℝ H x y = e * fderiv ℝ H x x := by
    conv_lhs => rw [hyeq]
    rw [map_smul, smul_eq_mul]
  set as := fderiv ℝ (fun z => aCoord H (u z)) z 1
  set at' := fderiv ℝ (fun z => aCoord H (u z)) z Complex.I
  set ws := fderiv ℝ (fun z => proj H (u z)) z 1
  set wt := fderiv ℝ (fun z => proj H (u z)) z Complex.I
  have e1 := congrArg (fderiv ℝ H x) hdb
  have e2 := congrArg (liouvilleCLM x) hdb
  rw [map_add, hJA, map_zero] at e1
  rw [map_add, hJL, map_zero] at e2
  rw [hfu 1, hfu Complex.I] at e1 e2
  simp only [map_add, map_smul, smul_eq_mul, hLx, hAw, hAy] at e1 e2
  simp only [ds, dt, ← liouvilleCLM_apply]
  change as = (liouvilleCLM x) wt ∧ at' = -(liouvilleCLM x) ws
  have hAx' := hAx.ne'
  constructor
  · have : 2 * e * fderiv ℝ H x x * (as - r * e * liouvilleCLM x wt) = 0 := by linear_combination e1
    rw [hre, one_mul] at this
    have h3 : 2 * e * fderiv ℝ H x x ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp this).resolve_left h3]
  · have k : r / (2 * fderiv ℝ H x x) * (e * (2 * at') * fderiv ℝ H x x + e * 0) * r⁻¹ = e * at' := by
      field_simp; ring
    have : e * (liouvilleCLM x ws + at') = 0 := by
      have := e2; simp only [mul_zero, zero_add, add_zero] at this k ⊢; linear_combination this - k
    linarith [(mul_eq_zero.mp this).resolve_left hepos.ne']

end DP

end S_DP_c

-- ===== DP_d =====
section S_DP_d


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

variable {n : ℕ}

noncomputable def omB : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V n) (F' := ℝ)).toLinearMap.comp
      (LinearMap.mk₂ ℝ omega0 omega0_add_left (fun c u v => by rw [omega0_smul_left]; rfl)
        omega0_add_right (fun c u v => by rw [omega0_smul_right]; rfl)))

@[simp] lemma omB_apply (p q : V n) : omB p q = omega0 p q := rfl

lemma fderiv_omega0 {f g : ℂ → V n} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    fderiv ℝ (fun z => omega0 (f z) (g z)) z v =
      omega0 (fderiv ℝ f z v) (g z) + omega0 (f z) (fderiv ℝ g z v) := by
  have h := omB.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt
  simp only [omB_apply] at h
  rw [h.fderiv]
  simp [add_comm]

lemma diff_om {f g : ℂ → V n} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : DifferentiableAt ℝ (fun z => omega0 (f z) (g z)) z := by
  have h := omB.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt
  simp only [omB_apply] at h
  exact h.differentiableAt

/-- derivative of `z ↦ fderiv f z c` -/
lemma fderiv_dir {f : ℂ → V n} (hf : ContDiff ℝ ∞ f) (c v z : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have h := h1.hasFDerivAt.clm_apply (hasFDerivAt_const c z)
  rw [h.fderiv]; simp

lemma fderiv_dir_real {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (c v z : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have h := h1.hasFDerivAt.clm_apply (hasFDerivAt_const c z)
  rw [h.fderiv]; simp

lemma symm2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    (hf : ContDiff ℝ ∞ f) (z v w : ℂ) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v :=
  (hf.contDiffAt.isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)) v w

/-- `g = ∂ₛa - i ∂ₜa` is holomorphic when `a` is harmonic. -/
theorem g_differentiable (a : ℂ → ℝ) (w : ℂ → V n) (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w)
    (hcr : ∀ z, ds a z = liouville (w z) (dt w z) ∧ dt a z = -liouville (w z) (ds w z))
    (hd : ∀ z, omega0 (ds w z) (dt w z) = 0) :
    Differentiable ℂ (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)) := by
  intro z
  have hP : (fun z => fderiv ℝ a z 1) = fun z => (1/2:ℝ) * omega0 (w z) (fderiv ℝ w z Complex.I) :=
    funext fun z => by rw [show fderiv ℝ a z 1 = ds a z from rfl, (hcr z).1, liouville, dt]; ring
  have hQ : (fun z => fderiv ℝ a z Complex.I) = fun z => (-1/2:ℝ) * omega0 (w z) (fderiv ℝ w z 1) :=
    funext fun z => by rw [show fderiv ℝ a z Complex.I = dt a z from rfl, (hcr z).2, liouville, ds]; ring
  have hwd : ∀ c : ℂ, Differentiable ℝ (fun z => fderiv ℝ w z c) := fun c =>
    ((hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hwz : DifferentiableAt ℝ w z := hw.differentiable (by simp) z
  -- Laplacian
  have hlap : fderiv ℝ (fderiv ℝ a) z 1 1 + fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I = 0 := by
    rw [← fderiv_dir_real ha, ← fderiv_dir_real ha, hP, hQ]
    rw [fderiv_const_mul (diff_om hwz (hwd _ z)), fderiv_const_mul (diff_om hwz (hwd _ z))]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_omega0 hwz (hwd _ z), fderiv_omega0 hwz (hwd _ z), fderiv_dir hw, fderiv_dir hw,
      symm2 hw z 1 Complex.I, omega0_anti (fderiv ℝ w z Complex.I)]
    have := hd z; simp only [ds, dt] at this
    linear_combination this
  have had : ∀ c : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ a z c) z := fun c =>
    (((ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) z
  have h1 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z 1)).comp z (had 1).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z Complex.I)).comp z
    (had Complex.I).hasFDerivAt
  have hg := h1.sub (h2.const_mul Complex.I)
  set D := Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z 1) z) -
    Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z Complex.I) z) with hD
  have hB : D Complex.I = Complex.I • D 1 := by
    simp only [hD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    rw [fderiv_dir_real ha, fderiv_dir_real ha, fderiv_dir_real ha, fderiv_dir_real ha,
      symm2 ha z Complex.I 1]
    have hl : (fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I : ℂ) =
        -(fderiv ℝ (fderiv ℝ a) z 1 1 : ℂ) := by
      rw [← Complex.ofReal_neg]; congr 1; linarith
    rw [hl]
    ring_nf; rw [Complex.I_sq]; ring
  let D' : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (D 1)
  refine (hasFDerivAt_of_restrictScalars ℝ (g' := D) (f' := D') hg ?_).differentiableAt
  ext v
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  simp only [D', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply]
  calc v • D 1 = ((v.re:ℂ) + v.im * Complex.I) • D 1 := by rw [Complex.re_add_im]
   _ = v.re • D 1 + v.im • (Complex.I • D 1) := by
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
   _ = D v := by rw [← hB, ← map_smul, ← map_smul, ← map_add, ← hv]

end DP

end S_DP_d

-- ===== DP_e =====
section S_DP_e


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DP

lemma det_mul (c : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight c).restrictScalars ℝ).det = Complex.normSq c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have e : (((1 : ℂ →L[ℂ] ℂ).smulRight c : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) = c • LinearMap.id := by
    ext; simp
  rw [e, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]; simp

lemma vol_rect (x0 y0 h k : ℝ) (hk : 0 ≤ k) (hh : 0 ≤ h) :
    volume (Complex.measurableEquivRealProd ⁻¹' (Ioo (x0 - h) (x0 + h) ×ˢ Ioo (y0 - k) (y0 + k))) =
      ENNReal.ofReal (2 * h) * ENNReal.ofReal (2 * k) := by
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  congr 2 <;> ring

noncomputable def phiC (m : ℝ) (t : ℝ) : ℝ := Real.arctan (t - m) / Real.pi + 1 / 2

lemma phiC_adm (m : ℝ) : Admissible (phiC m) := by
  refine ⟨?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · unfold phiC
    exact ((Real.contDiff_arctan.comp (contDiff_id.sub contDiff_const)).div_const _).add contDiff_const
  · intro s t hst
    unfold phiC
    have := Real.arctan_strictMono.monotone (sub_le_sub_right hst m)
    gcongr
  · unfold phiC
    have := Real.neg_pi_div_two_lt_arctan (t - m)
    have hp := Real.pi_pos
    rw [div_add' _ _ _ hp.ne']; apply div_nonneg _ hp.le; linarith
  · unfold phiC
    have := Real.arctan_lt_pi_div_two (t - m)
    have hp := Real.pi_pos
    rw [div_add' _ _ _ hp.ne', div_le_one hp]; linarith

lemma deriv_phiC (m t : ℝ) : deriv (phiC m) t = 1 / (1 + (t - m) ^ 2) / Real.pi := by
  have h := ((((hasDerivAt_id' t).sub_const m).arctan).div_const Real.pi).add_const (1/2 : ℝ)
  unfold phiC
  rw [h.deriv]; simp

lemma deriv_phiC_ge (m t : ℝ) (h : |t - m| < 1) : 1 / (2 * Real.pi) ≤ deriv (phiC m) t := by
  rw [deriv_phiC]
  have hp := Real.pi_pos
  have h2 : (t - m) ^ 2 ≤ 1 := by
    have := sq_abs (t - m); nlinarith [abs_nonneg (t - m)]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end DP

end S_DP_e

-- ===== DP_bloch =====
section S_DP_bloch


open Set Metric Filter Topology

namespace SchottkyDev

/-- **Bloch's theorem** (quantitative form, constant `1/128`): a holomorphic function on a disc
of radius `s` covers some disc of radius `s ‖f' z‖ / 128`. -/
theorem bloch (f : ℂ → ℂ) (z : ℂ) (s : ℝ) (hs : 0 < s)
    (hf : DifferentiableOn ℂ f (ball z s)) :
    ∃ b, ball b (s * ‖deriv f z‖ / 128) ⊆ f '' ball z s := by
  rcases eq_or_ne (deriv f z) 0 with h0 | h0
  · exact ⟨0, by simp [h0]⟩
  have hfa : AnalyticOnNhd ℂ f (ball z s) := hf.analyticOnNhd isOpen_ball
  have hdc : ContinuousOn (deriv f) (ball z s) := hfa.deriv.continuousOn
  set K := closedBall z (s / 2) with hK
  have hKsub : K ⊆ ball z s := closedBall_subset_ball (by linarith)
  have hKc : IsCompact K := isCompact_closedBall _ _
  let u : ℂ → ℝ := fun w => (s / 2 - dist w z) * ‖deriv f w‖
  have hu : ContinuousOn u K :=
    ((continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn)).mul
      ((hdc.mono hKsub).norm)
  have hzK : z ∈ K := mem_closedBall_self (by linarith)
  obtain ⟨a, haK, hamax⟩ := hKc.exists_isMaxOn ⟨z, hzK⟩ hu
  have hua : u z ≤ u a := hamax hzK
  have huz : u z = s / 2 * ‖deriv f z‖ := by simp [u]
  have huz_pos : 0 < u z := by rw [huz]; positivity
  have hdpos : 0 < s / 2 - dist a z := by
    by_contra hcon
    push Not at hcon
    have : u a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (norm_nonneg _)
    linarith
  set d := s / 2 - dist a z with hd
  set A := ‖deriv f a‖ with hA
  have hApos : 0 < A := by
    by_contra hcon
    push Not at hcon
    have : u a ≤ 0 := by
      show d * A ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos hdpos.le hcon
    linarith
  set ρ := d / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  -- derivative bound on the closed ball of radius ρ about a
  have hball_sub : closedBall a ρ ⊆ K := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have := dist_triangle w a z
    linarith
  have hderiv_bd : ∀ w ∈ closedBall a ρ, ‖deriv f w‖ ≤ 2 * A := by
    intro w hw
    have hwK := hball_sub hw
    have h1 : u w ≤ u a := hamax hwK
    have hw' : dist w z ≤ dist a z + ρ := by
      have := dist_triangle w a z
      rw [mem_closedBall] at hw
      linarith
    have h2 : ρ ≤ s / 2 - dist w z := by linarith
    have h3 : ρ * ‖deriv f w‖ ≤ u w := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : u a = 2 * ρ * A := by simp only [u, hA]; rw [← hd]; ring
    nlinarith
  -- Schwarz lemma applied to f' - f'(a)
  have hsub_ball : ball a ρ ⊆ ball z s := ball_subset_closedBall.trans (hball_sub.trans hKsub)
  have hschw : ∀ w ∈ ball a ρ, ‖deriv f w - deriv f a‖ ≤ 3 * A / ρ * ‖w - a‖ := by
    intro w hw
    have hd' : DifferentiableOn ℂ (deriv f) (ball a ρ) :=
      (hfa.deriv.differentiableOn).mono hsub_ball
    have hmaps : MapsTo (deriv f) (ball a ρ) (closedBall (deriv f a) (3 * A)) := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm]
      have := hderiv_bd x (ball_subset_closedBall hx)
      calc ‖deriv f x - deriv f a‖ ≤ ‖deriv f x‖ + ‖deriv f a‖ := norm_sub_le _ _
        _ ≤ 3 * A := by rw [← hA]; linarith
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd' hmaps hw
    simpa [dist_eq_norm] using this
  set t := ρ / 8 with ht
  have htpos : 0 < t := by positivity
  have htρ : t < ρ := by linarith
  have hcl_sub : closedBall a t ⊆ ball a ρ := closedBall_subset_ball htρ
  -- k(w) = f w - f a - f'(a) (w - a) is (A/2)-Lipschitz on closedBall a t
  have hk : ∀ w ∈ closedBall a t,
      ‖(f w - deriv f a * w) - (f a - deriv f a * a)‖ ≤ A / 2 * ‖w - a‖ := by
    intro w hw
    have hdiff : ∀ x ∈ closedBall a t, DifferentiableAt ℂ (fun x => f x - deriv f a * x) x := by
      intro x hx
      have : DifferentiableAt ℂ f x :=
        hf.differentiableAt (isOpen_ball.mem_nhds (hsub_ball (hcl_sub hx)))
      exact this.sub ((differentiableAt_id).const_mul _)
    have hbound : ∀ x ∈ closedBall a t, ‖deriv (fun x => f x - deriv f a * x) x‖ ≤ A / 2 := by
      intro x hx
      have hfx : DifferentiableAt ℂ f x :=
        hf.differentiableAt (isOpen_ball.mem_nhds (hsub_ball (hcl_sub hx)))
      have : deriv (fun x => f x - deriv f a * x) x = deriv f x - deriv f a := by
        have := ((hfx.hasDerivAt).sub ((hasDerivAt_id x).const_mul (deriv f a))).deriv
        rw [mul_one] at this
        exact this
      rw [this]
      have h1 := hschw x (hcl_sub hx)
      have h2 : ‖x - a‖ ≤ t := by rw [← dist_eq_norm]; exact hx
      calc ‖deriv f x - deriv f a‖ ≤ 3 * A / ρ * ‖x - a‖ := h1
        _ ≤ 3 * A / ρ * t := by gcongr
        _ ≤ A / 2 := by rw [ht]; field_simp; nlinarith
    exact (convex_closedBall a t).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (mem_closedBall_self htpos.le) hw
  -- lower bound on the sphere
  have hsphere : ∀ w ∈ sphere a t, A * t / 2 ≤ ‖f w - f a‖ := by
    intro w hw
    have hw' : w ∈ closedBall a t := sphere_subset_closedBall hw
    have h1 := hk w hw'
    have h2 : ‖w - a‖ = t := by rw [← dist_eq_norm]; exact hw
    have h3 : ‖deriv f a * (w - a)‖ = A * t := by rw [norm_mul, h2]
    have : f w - f a = deriv f a * (w - a) +
        ((f w - deriv f a * w) - (f a - deriv f a * a)) := by ring
    rw [this]
    have := norm_sub_norm_le (deriv f a * (w - a))
      (-((f w - deriv f a * w) - (f a - deriv f a * a)))
    rw [norm_neg, sub_neg_eq_add] at this
    rw [h2] at h1
    linarith
  have hdcl : DiffContOnCl ℂ f (ball a t) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a htpos.ne']
    exact hf.mono (hcl_sub.trans hsub_ball)
  have hfreq : ∃ᶠ w in 𝓝 a, f w ≠ f a := by
    intro hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hεf⟩ := hev
    set r := min ε t / 2 with hr
    have hrpos : 0 < r := by positivity
    have hrε : r < ε := by have := min_le_left ε t; linarith
    have hrt : r ≤ t := by have := min_le_right ε t; linarith
    have hw : dist (a + r) a = r := by simp [abs_of_pos hrpos]
    have hfeq : f (a + r) = f a := not_not.mp (hεf (by rw [hw]; exact hrε))
    have h1 := hk (a + r) (by rw [mem_closedBall, hw]; exact hrt)
    have h2 : ‖(a + r) - a‖ = r := by rw [← dist_eq_norm]; exact hw
    rw [h2, hfeq] at h1
    have : (f a - deriv f a * (a + ↑r)) - (f a - deriv f a * a) = -(deriv f a * r) := by ring
    rw [this, norm_neg, norm_mul] at h1
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] at h1
    rw [← hA] at h1
    nlinarith
  have himg := hdcl.ball_subset_image_closedBall htpos hsphere hfreq
  refine ⟨f a, ?_⟩
  intro v hv
  have hv' : v ∈ ball (f a) (A * t / 2 / 2) := by
    refine mem_of_mem_of_subset hv (ball_subset_ball ?_)
    have h4 : u a = 2 * ρ * A := by simp only [u, hA]; rw [← hd]; ring
    rw [huz] at hua
    rw [ht]
    nlinarith
  obtain ⟨w, hw, rfl⟩ := himg hv'
  exact ⟨w, hsub_ball (hcl_sub hw), rfl⟩

end SchottkyDev

end S_DP_bloch

-- ===== DP_f =====
section S_DP_f


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DP

theorem grad_zero (a : ℂ → ℝ) (ha : ContDiff ℝ ∞ a)
    (hg : Differentiable ℂ (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)))
    (E : ℝ≥0∞) (hE : E < ⊤)
    (hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z, ENNReal.ofReal (deriv φ (a z) * ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ E)
    (z : ℂ) : fderiv ℝ a z 1 = 0 ∧ fderiv ℝ a z Complex.I = 0 := by
  set g := fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ) with hgdef
  have hgre : ∀ z, (g z).re = fderiv ℝ a z 1 := fun z => by simp [g]
  have hgim : ∀ z, (g z).im = -fderiv ℝ a z Complex.I := fun z => by simp [g]
  have hN : ∀ z, Complex.normSq (g z) = (fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2 := by
    intro z; rw [Complex.normSq_apply, hgre, hgim]; ring
  obtain ⟨F, hF⟩ := hg.isExactOn_univ
  have hF' : ∀ z, HasDerivAt F (g z) z := fun z => hF z (mem_univ z)
  have hFd : Differentiable ℂ F := fun z => (hF' z).differentiableAt
  -- Re F - a is constant
  have hRe : ∀ z, HasFDerivAt (fun z => (F z).re - a z) (0 : ℂ →L[ℝ] ℝ) z := by
    intro z
    have h1 := Complex.reCLM.hasFDerivAt.comp z ((hF' z).hasFDerivAt.restrictScalars ℝ)
    have h2 := (ha.differentiable (by simp) z).hasFDerivAt
    refine (h1.sub h2).congr_fderiv ?_
    ext v
    have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
    have hav : fderiv ℝ a z v = v.re * fderiv ℝ a z 1 + v.im * fderiv ℝ a z Complex.I := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply, hav, smul_eq_mul,
      Complex.mul_re, hgre, hgim]
    ring
  have hconst := is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun z => (hRe z).differentiableAt)
    (fun z => (hRe z).fderiv)
  set c := (F 0).re - a 0
  have hreF : ∀ z, (F z).re = a z + c := fun z => by have := hconst z 0; linarith
  by_contra hne
  have hg0 : g z ≠ 0 := by
    intro h; apply hne
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    rw [hgre] at h1; rw [hgim] at h2; simp at h1 h2; exact ⟨h1, h2⟩
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr hg0
  set K := E.toReal
  have hEK : E = ENNReal.ofReal K := (ENNReal.ofReal_toReal hE.ne).symm
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  set ρ : ℝ := K * Real.pi / 2 + 2 with hρ
  set s : ℝ := 128 * ρ / ‖g z‖ with hs
  have hρpos : 0 < ρ := by positivity
  have hρ2 : 2 ≤ ρ := by rw [hρ]; have := Real.pi_pos; nlinarith
  have hspos : 0 < s := by positivity
  obtain ⟨b, hb⟩ := SchottkyDev.bloch F z s hspos hFd.differentiableOn
  rw [(hF' z).deriv, show s * ‖g z‖ / 128 = ρ by rw [hs]; field_simp] at hb
  set m := b.re - c
  have hφ := phiC_adm m
  set S := ball z s ∩ {z | |(F z).re - b.re| < 1} with hSdef
  have hSo : IsOpen S := isOpen_ball.inter
    (isOpen_lt ((Complex.continuous_re.comp hFd.continuous).sub continuous_const).abs continuous_const)
  -- rectangle
  set Rect := Complex.measurableEquivRealProd ⁻¹'
    (Ioo (b.re - 1) (b.re + 1) ×ˢ Ioo (b.im - (ρ - 1)) (b.im + (ρ - 1))) with hRect
  have hRS : Rect ⊆ F '' S := by
    intro v hv
    simp only [hRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo] at hv
    have hvb : v ∈ ball b ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖v - b‖ ≤ |(v - b).re| + |(v - b).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < 1 + (ρ - 1) := by
          simp only [Complex.sub_re, Complex.sub_im]
          gcongr <;> rw [abs_lt] <;> constructor <;> linarith
        _ = ρ := by ring
    obtain ⟨x, hx, hxv⟩ := hb hvb
    refine ⟨x, ⟨hx, ?_⟩, hxv⟩
    simp only [mem_setOf_eq, hxv]; rw [abs_lt]; constructor <;> linarith
  have hvol : ENNReal.ofReal (2 * 1) * ENNReal.ofReal (2 * (ρ - 1)) ≤
      ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| := by
    rw [← vol_rect b.re b.im 1 (ρ - 1) (by linarith) zero_le_one]
    refine (measure_mono hRS).trans ?_
    refine addHaar_image_le_lintegral_abs_det_fderiv volume hSo.measurableSet fun x _ => ?_
    exact ((hF' x).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hpt : ∀ x ∈ S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
        ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) := by
    intro x hx
    rw [det_mul, abs_of_nonneg (Complex.normSq_nonneg _), hN, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : |a x - m| < 1 := by
      have := hx.2; simp only [mem_setOf_eq, hreF] at this
      have e : a x - m = a x + c - b.re := by simp only [m]; ring
      rw [e]; exact this
    have h2 := deriv_phiC_ge m (a x) h1
    have hp := Real.pi_pos
    have h3 : 1 ≤ 2 * Real.pi * deriv (phiC m) (a x) := by
      rw [div_le_iff₀ (by positivity)] at h2; linarith
    have h4 : 0 ≤ (fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2 := by positivity
    nlinarith
  have hint : ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * E := by
    calc _ ≤ ∫⁻ x in S, ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) :=
          setLIntegral_mono' hSo.measurableSet hpt
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x in S, ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact (setLIntegral_le_lintegral _ _).trans (hbound _ hφ)
  have key := hvol.trans hint
  rw [hEK, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have hp := Real.pi_pos
  rw [hρ] at key
  nlinarith

end DP

end S_DP_f

-- ===== DQ_c =====
section S_DQ_c


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

/-! Local (open set `U`) versions of the DP_c / DP_d lemmas. -/

namespace DQ

open DP

variable {n : ℕ}

lemma smooth_aw (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (u : ℂ → V n)
    (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) U ∧ ContDiffOn ℝ ∞ (fun z => proj H (u z)) U := by
  obtain ⟨-, hP, hAc, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  exact ⟨hAc.comp hsm hu0, hP.comp hsm hu0⟩

lemma fderiv_u (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) (z : ℂ) (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ u z v = (Real.exp (2 * aCoord H (u z)) * (2 * fderiv ℝ (fun z => aCoord H (u z)) z v)) •
        proj H (u z) + Real.exp (2 * aCoord H (u z)) • fderiv ℝ (fun z => proj H (u z)) z v := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hA := ((ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hW := ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hE := (hA.const_mul 2).exp
  have hD := hE.smul hW
  have hD' : HasFDerivAt u _ z :=
    hD.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => (hrel _ (hu0 w hw)).2)
  rw [hD'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  abel

lemma dH_w (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) (z : ℂ) (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z v) = 0 := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨-, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hW := ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hc := (hH.1.differentiable (by simp) (proj H (u z))).hasFDerivAt.comp z hW
  have h2 : HasFDerivAt (fun z => H (proj H (u z))) (0 : ℂ →L[ℝ] ℝ) z :=
    (hasFDerivAt_const (1:ℝ) z).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => (hrel _ (hu0 w hw)).1)
  have := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hc.unique h2)
  simpa using this

theorem cr_rel (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z : ℂ) (hz : z ∈ U) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
      dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hdb := (hhol z hz).2
  simp only [JHolomorphic.dbarJ] at hdb
  have hx : H (proj H (u z)) = 1 := (hrel _ (hu0 z hz)).1
  have hyeq : u z = Real.exp (2 * aCoord H (u z)) • proj H (u z) := (hrel _ (hu0 z hz)).2
  obtain ⟨hJA, hJL⟩ := jtilde_AL H hH J hJ (u z) hx (fderiv ℝ u z Complex.I)
  have hfu := fderiv_u H hH J hJ U hU u hsm hu0 z hz
  have hAw := dH_w H hH J hJ U hU u hsm hu0 z hz
  set y := u z with hy
  set x := proj H y with hxdef
  set e := Real.exp (2 * aCoord H y) with he
  set r := scaleToS H y with hr
  have hre : r * e = 1 := by rw [he, exp_aCoord, ← hr, mul_inv_cancel₀ (scaleToS_pos H y).ne']
  have hrpos : 0 < r := scaleToS_pos H y
  have hepos : 0 < e := Real.exp_pos _
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hLx : liouvilleCLM x x = 0 := by rw [liouvilleCLM_apply, liouville, omega0_self]; simp
  have hAy : fderiv ℝ H x y = e * fderiv ℝ H x x := by
    conv_lhs => rw [hyeq]
    rw [map_smul, smul_eq_mul]
  set as := fderiv ℝ (fun z => aCoord H (u z)) z 1
  set at' := fderiv ℝ (fun z => aCoord H (u z)) z Complex.I
  set ws := fderiv ℝ (fun z => proj H (u z)) z 1
  set wt := fderiv ℝ (fun z => proj H (u z)) z Complex.I
  have e1 := congrArg (fderiv ℝ H x) hdb
  have e2 := congrArg (liouvilleCLM x) hdb
  rw [map_add, hJA, map_zero] at e1
  rw [map_add, hJL, map_zero] at e2
  rw [hfu 1, hfu Complex.I] at e1 e2
  simp only [map_add, map_smul, smul_eq_mul, hLx, hAw, hAy] at e1 e2
  simp only [ds, dt, ← liouvilleCLM_apply]
  change as = (liouvilleCLM x) wt ∧ at' = -(liouvilleCLM x) ws
  have hAx' := hAx.ne'
  constructor
  · have : 2 * e * fderiv ℝ H x x * (as - r * e * liouvilleCLM x wt) = 0 := by linear_combination e1
    rw [hre, one_mul] at this
    have h3 : 2 * e * fderiv ℝ H x x ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp this).resolve_left h3]
  · have k : r / (2 * fderiv ℝ H x x) * (e * (2 * at') * fderiv ℝ H x x + e * 0) * r⁻¹ = e * at' := by
      field_simp; ring
    have : e * (liouvilleCLM x ws + at') = 0 := by
      have := e2; simp only [mul_zero, zero_add, add_zero] at this k ⊢; linear_combination this - k
    linarith [(mul_eq_zero.mp this).resolve_left hepos.ne']

end DQ

end S_DQ_c

-- ===== DQ_d =====
section S_DQ_d


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff

namespace DQ

open DP

variable {n : ℕ}

lemma fderiv_dir_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (c v : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have h := h1.hasFDerivAt.clm_apply (hasFDerivAt_const c z)
  rw [h.fderiv]; simp

lemma diff_dir_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (c : ℂ) : DifferentiableAt ℝ (fun z => fderiv ℝ f z c) z :=
  ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)

lemma symm2_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v :=
  (hf.isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)) v w

theorem g_differentiableOn (U : Set ℂ) (hU : IsOpen U) (a : ℂ → ℝ) (w : ℂ → V n)
    (ha : ContDiffOn ℝ ∞ a U) (hw : ContDiffOn ℝ ∞ w U)
    (hcr : ∀ z ∈ U, ds a z = liouville (w z) (dt w z) ∧ dt a z = -liouville (w z) (ds w z))
    (hd : ∀ z ∈ U, omega0 (ds w z) (dt w z) = 0) :
    DifferentiableOn ℂ (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)) U := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hza := ha.contDiffAt (hU.mem_nhds hz)
  have hzw := hw.contDiffAt (hU.mem_nhds hz)
  have hP : (fun z => fderiv ℝ a z 1) =ᶠ[𝓝 z]
      fun z => (1/2:ℝ) * omega0 (w z) (fderiv ℝ w z Complex.I) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun z hz => by
      show fderiv ℝ a z 1 = _
      rw [show fderiv ℝ a z 1 = ds a z from rfl, (hcr z hz).1, liouville, dt]; ring
  have hQ : (fun z => fderiv ℝ a z Complex.I) =ᶠ[𝓝 z]
      fun z => (-1/2:ℝ) * omega0 (w z) (fderiv ℝ w z 1) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun z hz => by
      show fderiv ℝ a z Complex.I = _
      rw [show fderiv ℝ a z Complex.I = dt a z from rfl, (hcr z hz).2, liouville, ds]; ring
  have hwz : DifferentiableAt ℝ w z := hzw.differentiableAt (by simp)
  have hlap : fderiv ℝ (fderiv ℝ a) z 1 1 + fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I = 0 := by
    rw [← fderiv_dir_at hza, ← fderiv_dir_at hza, hP.fderiv_eq, hQ.fderiv_eq]
    rw [fderiv_const_mul (diff_om hwz (diff_dir_at hzw _)),
      fderiv_const_mul (diff_om hwz (diff_dir_at hzw _))]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_omega0 hwz (diff_dir_at hzw _), fderiv_omega0 hwz (diff_dir_at hzw _),
      fderiv_dir_at hzw, fderiv_dir_at hzw, symm2_at hzw 1 Complex.I,
      omega0_anti (fderiv ℝ w z Complex.I)]
    have := hd z hz; simp only [ds, dt] at this
    linear_combination this
  have h1 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z 1)).comp z (diff_dir_at hza 1).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt (x := fderiv ℝ a z Complex.I)).comp z
    (diff_dir_at hza Complex.I).hasFDerivAt
  have hg := h1.sub (h2.const_mul Complex.I)
  set D := Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z 1) z) -
    Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ a z Complex.I) z) with hD
  have hB : D Complex.I = Complex.I • D 1 := by
    simp only [hD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    rw [fderiv_dir_at hza, fderiv_dir_at hza, fderiv_dir_at hza, fderiv_dir_at hza,
      symm2_at hza Complex.I 1]
    have hl : (fderiv ℝ (fderiv ℝ a) z Complex.I Complex.I : ℂ) =
        -(fderiv ℝ (fderiv ℝ a) z 1 1 : ℂ) := by
      rw [← Complex.ofReal_neg]; congr 1; linarith
    rw [hl]
    ring_nf; rw [Complex.I_sq]; ring
  let D' : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (D 1)
  refine (hasFDerivAt_of_restrictScalars ℝ (g' := D) (f' := D') hg ?_).differentiableAt
  ext v
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  simp only [D', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply]
  calc v • D 1 = ((v.re:ℂ) + v.im * Complex.I) • D 1 := by rw [Complex.re_add_im]
   _ = v.re • D 1 + v.im • (Complex.I • D 1) := by
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
   _ = D v := by rw [← hB, ← map_smul, ← map_smul, ← map_add, ← hv]

end DQ

end S_DQ_d

-- ===== DQ_f =====
section S_DQ_f


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

/-- Local Bloch–energy bound: on a ball inside `U`, `s |g(z₀)| / 128 ≤ K π / 2 + 1`. -/
theorem grad_bound (U : Set ℂ) (hU : IsOpen U) (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a U)
    (hg : DifferentiableOn ℂ
      (fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)) U)
    (E : ℝ≥0∞) (hE : E < ⊤)
    (hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) * ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ E)
    (z : ℂ) (s : ℝ) (hspos : 0 < s) (hsub : ball z s ⊆ U) :
    s * ‖(fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)‖ / 128 ≤
      E.toReal * Real.pi / 2 + 1 := by
  set g := fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ) with hgdef
  change s * ‖g z‖ / 128 ≤ _
  have hgre : ∀ z, (g z).re = fderiv ℝ a z 1 := fun z => by simp [g]
  have hgim : ∀ z, (g z).im = -fderiv ℝ a z Complex.I := fun z => by simp [g]
  have hN : ∀ z, Complex.normSq (g z) = (fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2 := by
    intro z; rw [Complex.normSq_apply, hgre, hgim]; ring
  obtain ⟨F, hF'⟩ := (hg.mono hsub).isExactOn_ball
  have hFd : DifferentiableOn ℂ F (ball z s) := fun x hx => (hF' x hx).differentiableAt.differentiableWithinAt
  have hRe : ∀ x ∈ ball z s, HasFDerivAt (fun z => (F z).re - a z) (0 : ℂ →L[ℝ] ℝ) x := by
    intro x hx
    have h1 := Complex.reCLM.hasFDerivAt.comp x ((hF' x hx).hasFDerivAt.restrictScalars ℝ)
    have h2 := ((ha.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by simp)).hasFDerivAt
    refine (h1.sub h2).congr_fderiv ?_
    ext v
    have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
    have hav : fderiv ℝ a x v = v.re * fderiv ℝ a x 1 + v.im * fderiv ℝ a x Complex.I := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply, hav, smul_eq_mul,
      Complex.mul_re, hgre, hgim]
    ring
  set c := (F z).re - a z
  have hreF : ∀ x ∈ ball z s, (F x).re = a x + c := fun x hx => by
    have := isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (convex_ball z s).isPreconnected
      (fun y hy => (hRe y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hRe y hy).fderiv) hx (mem_ball_self hspos)
    linarith
  by_contra hne
  rw [not_le] at hne
  set K := E.toReal
  have hEK : E = ENNReal.ofReal K := (ENNReal.ofReal_toReal hE.ne).symm
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  set ρ : ℝ := s * ‖g z‖ / 128 with hρ
  have hρ2 : 1 ≤ ρ := by have := Real.pi_pos; nlinarith
  obtain ⟨b, hb⟩ := SchottkyDev.bloch F z s hspos hFd
  rw [(hF' z (mem_ball_self hspos)).deriv] at hb
  set m := b.re - c
  have hφ := phiC_adm m
  set S := ball z s ∩ F ⁻¹' {w | |w.re - b.re| < 1} with hSdef
  have hSo : IsOpen S := hFd.continuousOn.isOpen_inter_preimage isOpen_ball
    (isOpen_lt (Complex.continuous_re.sub continuous_const).abs continuous_const)
  set Rect := Complex.measurableEquivRealProd ⁻¹'
    (Ioo (b.re - 1) (b.re + 1) ×ˢ Ioo (b.im - (ρ - 1)) (b.im + (ρ - 1))) with hRect
  have hRS : Rect ⊆ F '' S := by
    intro v hv
    simp only [hRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo] at hv
    have hvb : v ∈ ball b ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖v - b‖ ≤ |(v - b).re| + |(v - b).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < 1 + (ρ - 1) := by
          simp only [Complex.sub_re, Complex.sub_im]
          gcongr <;> rw [abs_lt] <;> constructor <;> linarith
        _ = ρ := by ring
    obtain ⟨x, hx, hxv⟩ := hb hvb
    refine ⟨x, ⟨hx, ?_⟩, hxv⟩
    simp only [mem_preimage, mem_setOf_eq, hxv]; rw [abs_lt]; constructor <;> linarith
  have hvol : ENNReal.ofReal (2 * 1) * ENNReal.ofReal (2 * (ρ - 1)) ≤
      ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| := by
    rw [← vol_rect b.re b.im 1 (ρ - 1) (by linarith) zero_le_one]
    refine (measure_mono hRS).trans ?_
    refine addHaar_image_le_lintegral_abs_det_fderiv volume hSo.measurableSet fun x hx => ?_
    exact ((hF' x hx.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hpt : ∀ x ∈ S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
        ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) := by
    intro x hx
    rw [det_mul, abs_of_nonneg (Complex.normSq_nonneg _), hN, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : |a x - m| < 1 := by
      have := hx.2; simp only [mem_preimage, mem_setOf_eq, hreF x hx.1] at this
      have e : a x - m = a x + c - b.re := by simp only [m]; ring
      rw [e]; exact this
    have h2 := deriv_phiC_ge m (a x) h1
    have hp := Real.pi_pos
    have h3 : 1 ≤ 2 * Real.pi * deriv (phiC m) (a x) := by
      rw [div_le_iff₀ (by positivity)] at h2; linarith
    have h4 : 0 ≤ (fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2 := by positivity
    nlinarith
  have hSU : S ⊆ U := fun x hx => hsub hx.1
  have hint : ∫⁻ x in S, ENNReal.ofReal |(((1 : ℂ →L[ℂ] ℂ).smulRight (g x)).restrictScalars ℝ).det| ≤
      ENNReal.ofReal (2 * Real.pi) * E := by
    calc _ ≤ ∫⁻ x in S, ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) :=
          setLIntegral_mono' hSo.measurableSet hpt
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x in S, ENNReal.ofReal (deriv (phiC m) (a x) *
            ((fderiv ℝ a x 1) ^ 2 + (fderiv ℝ a x Complex.I) ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact (lintegral_mono_set hSU).trans (hbound _ hφ)
  have key := hvol.trans hint
  rw [hEK, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have hp := Real.pi_pos
  nlinarith

end DQ

end S_DQ_f

-- ===== DQ_g =====
section S_DQ_g


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

variable {n : ℕ}

/-- (A) vanishing `dλ`-energy on an open set forces the `dλ`-density to vanish pointwise. -/
theorem dens_zero (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (h0 : dlambdaEnergy H U u = 0) :
    ∀ z ∈ U, omega0 (ds (fun z => proj H (u z)) z) (dt (fun z => proj H (u z)) z) = 0 := by
  have hu' := hu
  obtain ⟨hsm, hu0, hhol, hE⟩ := hu
  obtain ⟨-, hnn2, -, -⟩ := energyDensity_nonneg H hH J hJ U hU u hu'
  obtain ⟨-, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hwd : ∀ c : ℂ, ContinuousOn (fun z => fderiv ℝ (fun z => proj H (u z)) z c) U := fun c =>
    (hw.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hcont : ContinuousOn (fun z => dlambdaDensity H u z) U := by
    have h2 : ContinuousOn (fun z => omB (fderiv ℝ (fun z => proj H (u z)) z 1)
        (fderiv ℝ (fun z => proj H (u z)) z Complex.I)) U :=
      (omB.continuous.comp_continuousOn (hwd 1)).clm_apply (hwd Complex.I)
    exact h2
  have hc2 : ContinuousOn (fun z => ENNReal.ofReal (dlambdaDensity H u z)) U :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hae : (fun z => ENNReal.ofReal (dlambdaDensity H u z)) =ᵐ[volume.restrict U] 0 :=
    (lintegral_eq_zero_iff' (hc2.aemeasurable hU.measurableSet)).mp h0
  have heq := Measure.eqOn_open_of_ae_eq hae hU hc2 continuousOn_const
  intro z hz
  have h1 : ENNReal.ofReal (dlambdaDensity H u z) = 0 := heq hz
  rw [ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (hnn2 z hz)

lemma jt_unfold (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (y v : V n) :
    Jtilde H J y v =
      (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) * fderiv ℝ H (proj H y) v) •
          ((scaleToS H y)⁻¹ • reeb H (proj H y)) -
        (scaleToS H y * liouvilleCLM (proj H y) v) • ((2:ℝ) • y) +
        J (proj H y) (v - (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) *
            fderiv ℝ H (proj H y) v) • ((2:ℝ) • y) -
          (scaleToS H y * liouvilleCLM (proj H y) v) • ((scaleToS H y)⁻¹ • reeb H (proj H y))) := by
  simp only [Jtilde, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- (C) the `ξ`-component: with vanishing `dλ`-density, `∂ₛw = -∂ₜa R(w)` and `∂ₜw = ∂ₛa R(w)`. -/
theorem xi_part (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hsm : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z : ℂ) (hz : z ∈ U)
    (hd : omega0 (ds (fun z => proj H (u z)) z) (dt (fun z => proj H (u z)) z) = 0) :
    ds (fun z => proj H (u z)) z = -(dt (fun z => aCoord H (u z)) z) • reeb H (proj H (u z)) ∧
      dt (fun z => proj H (u z)) z = (ds (fun z => aCoord H (u z)) z) • reeb H (proj H (u z)) := by
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hdb := (hhol z hz).2
  simp only [JHolomorphic.dbarJ] at hdb
  have hx : H (proj H (u z)) = 1 := (hrel _ (hu0 z hz)).1
  have hyeq : u z = Real.exp (2 * aCoord H (u z)) • proj H (u z) := (hrel _ (hu0 z hz)).2
  have hfu := fderiv_u H hH J hJ U hU u hsm hu0 z hz
  have hAw := dH_w H hH J hJ U hU u hsm hu0 z hz
  obtain ⟨hcr1, hcr2⟩ := cr_rel H hH J hJ U hU u hsm hu0 hhol z hz
  rw [jt_unfold] at hdb
  rw [hfu 1, hfu Complex.I] at hdb
  have hAwI := hAw Complex.I
  have hAw1 := hAw 1
  simp only [ds, dt] at hcr1 hcr2 hd ⊢
  set y := u z with hy
  set x := proj H y with hxdef
  set e := Real.exp (2 * aCoord H y) with he
  set r := scaleToS H y with hr
  have hrpos : 0 < r := scaleToS_pos H y
  have hepos : 0 < e := Real.exp_pos _
  have hre : r⁻¹ = e := by rw [he, exp_aCoord]
  have hxS : x ∈ energySurface H := hx
  obtain ⟨-, hLR, hAR, hωR⟩ := reeb_spec H hH x hxS
  have hAx : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hLx : liouvilleCLM x x = 0 := by rw [liouvilleCLM_apply, liouville, omega0_self]; simp
  have hLR' : liouvilleCLM x (reeb H x) = 1 := by rw [liouvilleCLM_apply]; exact hLR
  set as := fderiv ℝ (fun z => aCoord H (u z)) z 1
  set at' := fderiv ℝ (fun z => aCoord H (u z)) z Complex.I
  set ws := fderiv ℝ (fun z => proj H (u z)) z 1
  set wt := fderiv ℝ (fun z => proj H (u z)) z Complex.I
  set R := reeb H x
  set ζs := ws - liouvilleCLM x ws • R with hζs
  set ζt := wt - liouvilleCLM x wt • R with hζt
  have hxis : ∀ v, fderiv ℝ H x v = 0 → IsInXi H x (v - liouvilleCLM x v • R) := by
    intro v hv
    constructor
    · rw [← liouvilleCLM_apply]; simp only [map_sub, map_smul, smul_eq_mul, hLR']; ring
    · simp only [map_sub, map_smul, smul_eq_mul, hAR, hv]; ring
  have hXt : IsInXi H x ζt := hxis wt hAwI
  have hXs : IsInXi H x ζs := hxis ws hAw1
  have hα : r / (2 * fderiv ℝ H x x) * fderiv ℝ H x ((e * (2 * at')) • x + e • wt) = at' := by
    rw [map_add, map_smul, map_smul, hAwI, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
      ← hre]
    field_simp
  have hβ : r * liouvilleCLM x ((e * (2 * at')) • x + e • wt) = liouvilleCLM x wt := by
    rw [map_add, map_smul, map_smul, hLx, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, ← hre]
    field_simp
  rw [hα, hβ, hre, hyeq] at hdb
  have hinner : (e * (2 * at')) • x + e • wt - at' • ((2:ℝ) • e • x) - liouvilleCLM x wt • e • R =
      e • ζt := by
    simp only [hζt]; module
  rw [hinner, map_smul] at hdb
  rw [← liouvilleCLM_apply] at hcr1 hcr2
  change as = liouvilleCLM x wt at hcr1
  change at' = -liouvilleCLM x ws at hcr2
  have hsum : e • (ζs + J x ζt) = 0 := by
    rw [← hdb, hcr2, hζs, hcr1]; module
  have hJs : ζs = -J x ζt := by
    have := (smul_eq_zero.mp hsum).resolve_left hepos.ne'
    exact eq_neg_of_add_eq_zero_left this
  -- density in terms of ζ
  have hws : ws = liouvilleCLM x ws • R + ζs := by simp [hζs]
  have hwt : wt = liouvilleCLM x wt • R + ζt := by simp [hζt]
  have hRR : omega0 R R = 0 := omega0_self R
  have hRt : omega0 R ζt = 0 := hωR _ hXt.2
  have hRs : omega0 R ζs = 0 := hωR _ hXs.2
  have hsR : omega0 ζs R = 0 := by rw [omega0_anti, hRs, neg_zero]
  have hdens : omega0 ws wt = omega0 ζt (J x ζt) := by
    rw [hws, hwt]
    simp only [omega0_add_left, omega0_add_right, omega0_smul_left, omega0_smul_right, hRR, hRt,
      hsR, mul_zero, zero_add]
    rw [hJs, omega0_anti]
    rw [show -J x ζt = (-1:ℝ) • J x ζt by simp, omega0_smul_right]; ring
  have hζ0 : ζt = 0 := by
    by_contra hne
    have := ((hJ.2 x hxS ζt ζt hXt hXt).2.2.1 hne)
    rw [← hdens] at this; linarith
  have hζs0 : ζs = 0 := by rw [hJs, hζ0, map_zero, neg_zero]
  constructor
  · rw [hws, hζs0, add_zero, hcr2, neg_neg]
  · rw [hwt, hζ0, add_zero, hcr1]

end DQ

end S_DQ_g

-- ===== DQ_h =====
section S_DQ_h


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DQ

open DP

variable {n : ℕ}

lemma U_open : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne

lemma U_conn : IsPreconnected {z : ℂ | z ≠ 0} := by
  have := (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (0:ℂ)).isPreconnected
  convert this using 1
  ext z; simp

lemma clm_decomp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℂ →L[ℝ] F) (v : ℂ) :
    L v = v.re • L 1 + v.im • L Complex.I := by
  have hv : v = v.re • (1:ℂ) + v.im • Complex.I := by apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- Removable singularity + Liouville: `z g(z)` bounded on `ℂ \ {0}` is constant. -/
lemma punct_liouville (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z | z ≠ 0}) (M : ℝ)
    (hb : ∀ z : ℂ, z ≠ 0 → ‖z * g z‖ ≤ M) : ∀ z : ℂ, z ≠ 0 → z * g z = g 1 := by
  set f := fun z => z * g z with hf
  have hd : DifferentiableOn ℂ f (univ \ {0}) :=
    (differentiableOn_id.mul hg).mono (fun z hz => hz.2)
  have hbd : BddAbove (norm ∘ f '' (univ \ {0})) :=
    ⟨M, by rintro _ ⟨z, hz, rfl⟩; exact hb z hz.2⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove Filter.univ_mem hd hbd
  set F := Function.update f 0 (limUnder (𝓝[≠] (0:ℂ)) f) with hFdef
  have hF' : Differentiable ℂ F := fun z => (hF z (mem_univ z)).differentiableAt Filter.univ_mem
  have hFb : Bornology.IsBounded (range F) := by
    refine (isBounded_closedBall (x := (0:ℂ)) (r := max M ‖F 0‖)).subset ?_
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    by_cases hz : z = 0
    · subst hz; exact le_max_right _ _
    · rw [hFdef, Function.update_of_ne hz]; exact (hb z hz).trans (le_max_left _ _)
  intro z hz
  have := hF'.apply_eq_apply_of_bounded hFb z 1
  rw [hFdef, Function.update_of_ne hz, Function.update_of_ne one_ne_zero, hf] at this
  simpa using this

theorem a_w_formula (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J {z | z ≠ 0} u) (h0 : dlambdaEnergy H {z | z ≠ 0} u = 0) :
    ∃ α c0 : ℝ, (∀ z : ℂ, z ≠ 0 → aCoord H (u z) = α * Real.log ‖z‖ + c0) ∧
      (∀ z : ℂ, z ≠ 0 → ∀ v : ℂ,
        fderiv ℝ (fun z => proj H (u z)) z v = (α * (v / z).im) • reeb H (proj H (u z))) := by
  set U : Set ℂ := {z | z ≠ 0} with hUdef
  have hU : IsOpen U := U_open
  have hu' := hu
  obtain ⟨hsm, hu0, hhol, hE⟩ := hu
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hd := dens_zero H hH J hJ U hU u hu' h0
  have hcr := fun z hz => cr_rel H hH J hJ U hU u hsm hu0 hhol z hz
  have hg := g_differentiableOn U hU _ _ ha hw hcr hd
  set a := fun z => aCoord H (u z) with hadef
  set w := fun z => proj H (u z) with hwdef
  have hED : ∀ φ, ∀ z ∈ U, energyDensity H φ u z = deriv φ (a z) *
      ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2) := by
    intro φ z hz
    simp only [hadef, hwdef] at *
    have h1 := (hcr z hz).1; have h2 := (hcr z hz).2
    have hdz := hd z hz
    simp only [ds, dt] at h1 h2 hdz
    simp only [energyDensity, ds, dt, hdz, mul_zero, add_zero]
    rw [← h1]
    have h3 : liouville (proj H (u z)) ((fderiv ℝ (fun z => proj H (u z)) z) 1) =
      -(fderiv ℝ (fun z => aCoord H (u z)) z) Complex.I := by rw [h2]; ring
    rw [h3]; ring
  have hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) *
        ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ energy H U u := by
    intro φ hφ
    have : ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) *
        ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) =
        ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z) :=
      setLIntegral_congr_fun hU.measurableSet (fun z hz => by rw [hED φ z hz])
    rw [this]
    exact le_iSup₂ (f := fun φ (_ : Admissible φ) =>
      ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z)) φ hφ
  set g := fun z => (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ) with hgdef
  have hb : ∀ z : ℂ, z ≠ 0 → ‖z * g z‖ ≤ 128 * ((energy H U u).toReal * Real.pi / 2 + 1) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hsub : ball z ‖z‖ ⊆ U := by
      intro y hy
      simp only [hUdef, mem_setOf_eq]
      rintro rfl
      rw [mem_ball, dist_zero_left] at hy
      exact lt_irrefl _ hy
    have := grad_bound U hU a ha hg _ hE hbound z ‖z‖ hzpos hsub
    rw [norm_mul]
    change ‖z‖ * ‖g z‖ / 128 ≤ _ at this
    linarith
  have hκ := punct_liouville g hg _ hb
  set κ := g 1 with hκdef
  -- da(z) v = Re(g z * v)
  have hda : ∀ z : ℂ, z ≠ 0 → ∀ v : ℂ, fderiv ℝ a z v = (κ / z * v).re := by
    intro z hz v
    have hgz : g z = κ / z := by rw [← hκ z hz]; field_simp
    rw [← hgz, clm_decomp (fderiv ℝ a z) v]
    simp only [hgdef, smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    ring
  have hadiff : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ a z := fun z hz =>
    (ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  -- κ is real
  have hκim : κ.im = 0 := by
    set φ : ℝ → ℝ := fun t => a (Complex.exp (t * Complex.I)) + κ.im * t with hφ
    have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
        (Complex.exp (t * Complex.I) * Complex.I) t := by
      intro t
      have := ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).cexp
      simpa using this
    have hφd : ∀ t, HasDerivAt φ 0 t := by
      intro t
      have hne : Complex.exp (t * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have h1 := (hadiff _ hne).hasFDerivAt.comp_hasDerivAt t (hγ t)
      have h2 := h1.add ((hasDerivAt_id t).const_mul κ.im)
      have h3 : HasDerivAt φ (fderiv ℝ a (Complex.exp (t * Complex.I))
          (Complex.exp (t * Complex.I) * Complex.I) + κ.im * 1) t := h2
      convert h3 using 1
      rw [hda _ hne, show κ / Complex.exp (t * Complex.I) * (Complex.exp (t * Complex.I) * Complex.I)
        = κ * Complex.I by field_simp]
      simp
    have hc := is_const_of_deriv_eq_zero (fun t => (hφd t).differentiableAt)
      (fun t => (hφd t).deriv) (2 * Real.pi) 0
    simp only [hφ] at hc
    have he : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp (((0:ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [he] at hc
    have := Real.pi_pos
    nlinarith
  set α := κ.re with hαdef
  have hκα : κ = (α : ℂ) := Complex.ext (by simp [hαdef]) (by simp [hκim])
  -- a = α log ‖z‖ + c0
  have hlog : ∀ z : ℂ, z ≠ 0 → HasFDerivAt (fun z : ℂ => Real.log (‖z‖ ^ 2))
      ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z := by
    intro z hz
    exact (hasStrictFDerivAt_norm_sq z).hasFDerivAt.log (by positivity)
  have hG : ∀ z ∈ U, HasFDerivAt (fun z => a z - α / 2 * Real.log (‖z‖ ^ 2)) (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    refine ((hadiff z hz).hasFDerivAt.sub ((hlog z hz).const_mul (α / 2))).congr_fderiv ?_
    ext1 v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, hda z hz v, hκα]
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq]
    have hn : Complex.normSq z ≠ 0 := Complex.normSq_pos.mpr hz |>.ne'
    rw [div_mul_eq_mul_div, Complex.div_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, nsmul_eq_mul]
    field_simp
    ring
  have hGc : ∀ z ∈ U, a z - α / 2 * Real.log (‖z‖ ^ 2) = a 1 - α / 2 * Real.log (‖(1:ℂ)‖ ^ 2) :=
    fun z hz => hU.is_const_of_fderiv_eq_zero (𝕜 := ℝ) U_conn
      (fun y hy => (hG y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hG y hy).fderiv) hz (by simp [hUdef])
  refine ⟨α, a 1, fun z hz => ?_, fun z hz v => ?_⟩
  · have := hGc z hz
    rw [Real.log_pow] at this
    simp only [norm_one, one_pow, Real.log_one, mul_zero, sub_zero] at this
    change a z = _
    push_cast at this
    linarith
  · obtain ⟨hws, hwt⟩ := xi_part H hH J hJ U hU u hsm hu0 hhol z hz (hd z hz)
    simp only [ds, dt] at hws hwt
    rw [clm_decomp, hws, hwt, ← hadef]
    have e1 := hda z hz 1
    have e2 := hda z hz Complex.I
    rw [e1, e2, hκα, smul_smul, smul_smul, ← add_smul]
    congr 1
    have hn : Complex.normSq z ≠ 0 := Complex.normSq_pos.mpr hz |>.ne'
    simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.div_re]
    field_simp
    ring

end DQ

end S_DQ_h

-- ===== DR_a =====
section S_DR_a


open Set Metric Filter Topology MeasureTheory
open FiniteEnergyPlane
open scoped ContDiff ENNReal

namespace DR

open DP DQ

variable {n : ℕ}

noncomputable def gfun (a : ℂ → ℝ) (z : ℂ) : ℂ := (fderiv ℝ a z 1 : ℂ) - Complex.I * (fderiv ℝ a z Complex.I : ℂ)

theorem core (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (h0 : dlambdaEnergy H U u = 0) :
    DifferentiableOn ℂ (gfun fun z => aCoord H (u z)) U ∧
      (∃ M : ℝ, ∀ z ∈ U, ∀ s : ℝ, 0 < s → ball z s ⊆ U →
        s * ‖gfun (fun z => aCoord H (u z)) z‖ ≤ M) ∧
      (∀ z ∈ U, ∀ v : ℂ, fderiv ℝ (fun z => aCoord H (u z)) z v =
        (gfun (fun z => aCoord H (u z)) z * v).re) ∧
      (∀ z ∈ U, ∀ v : ℂ, fderiv ℝ (fun z => proj H (u z)) z v =
        (gfun (fun z => aCoord H (u z)) z * v).im • reeb H (proj H (u z))) := by
  have hu' := hu
  obtain ⟨hsm, hu0, hhol, hE⟩ := hu
  obtain ⟨ha, hw⟩ := smooth_aw H hH J hJ U u hsm hu0
  have hd := dens_zero H hH J hJ U hU u hu' h0
  have hcr := fun z hz => cr_rel H hH J hJ U hU u hsm hu0 hhol z hz
  have hg := g_differentiableOn U hU _ _ ha hw hcr hd
  set a := fun z => aCoord H (u z) with hadef
  set w := fun z => proj H (u z) with hwdef
  have hED : ∀ φ, ∀ z ∈ U, energyDensity H φ u z = deriv φ (a z) *
      ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2) := by
    intro φ z hz
    simp only [hadef, hwdef] at *
    have h1 := (hcr z hz).1; have h2 := (hcr z hz).2
    have hdz := hd z hz
    simp only [ds, dt] at h1 h2 hdz
    simp only [energyDensity, ds, dt, hdz, mul_zero, add_zero]
    rw [← h1]
    have h3 : liouville (proj H (u z)) ((fderiv ℝ (fun z => proj H (u z)) z) 1) =
      -(fderiv ℝ (fun z => aCoord H (u z)) z) Complex.I := by rw [h2]; ring
    rw [h3]; ring
  have hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) *
        ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) ≤ energy H U u := by
    intro φ hφ
    have : ∫⁻ z in U, ENNReal.ofReal (deriv φ (a z) *
        ((fderiv ℝ a z 1) ^ 2 + (fderiv ℝ a z Complex.I) ^ 2)) =
        ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z) :=
      setLIntegral_congr_fun hU.measurableSet (fun z hz => by rw [hED φ z hz])
    rw [this]
    exact le_iSup₂ (f := fun φ (_ : Admissible φ) =>
      ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z)) φ hφ
  have hda : ∀ z ∈ U, ∀ v : ℂ, fderiv ℝ a z v = (gfun a z * v).re := by
    intro z hz v
    rw [clm_decomp (fderiv ℝ a z) v]
    simp only [gfun, smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    ring
  refine ⟨hg, ⟨128 * ((energy H U u).toReal * Real.pi / 2 + 1), fun z hz s hs hsub => ?_⟩, hda,
    fun z hz v => ?_⟩
  · have := grad_bound U hU a ha hg _ hE hbound z s hs hsub
    change s * ‖gfun a z‖ / 128 ≤ _ at this
    linarith
  · obtain ⟨hws, hwt⟩ := xi_part H hH J hJ U hU u hsm hu0 hhol z hz (hd z hz)
    simp only [ds, dt] at hws hwt
    rw [clm_decomp, hws, hwt, smul_smul, smul_smul, ← add_smul]
    congr 1
    simp only [gfun, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    ring

end DR

end S_DR_a

-- ===== DR_d =====
section S_DR_d


open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff NNReal

namespace DR

open DP

variable {n : ℕ}

lemma reeb_contDiffAt (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ 1 (reeb H) x := by
  have hgrad : ContDiff ℝ 1 (grad H) := by
    refine contDiff_pi.2 fun k => ?_
    exact (hH.1.fderiv_right (m := 1) (by
      exact WithTop.coe_le_coe.mpr le_top)).clm_apply contDiff_const
  have hX : ContDiff ℝ 1 (hamVF H) := (j0L (n := n)).contDiff.comp hgrad
  have hL : ContDiff ℝ 1 (fun x => liouville x (hamVF H x)) := by
    have : (fun x => liouville x (hamVF H x)) = fun x => (1/2:ℝ) * omB x (hamVF H x) := by
      ext x; simp only [liouville, omB_apply]; ring
    rw [this]
    exact contDiff_const.mul (omB.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk hX))
  have hpos := (reeb_spec H hH x hx).1
  exact (hL.contDiffAt.inv hpos.ne').smul hX.contDiffAt

lemma lip_smul {N : Set (V n)} {K : ℝ≥0} {R : V n → V n} (hK : LipschitzOnWith K R N) (c : ℝ) :
    LipschitzOnWith (‖c‖₊ * K) (fun y => c • R y) N :=
  LipschitzOnWith.of_dist_le_mul fun a ha b hb => by
    rw [dist_smul₀]; push_cast; rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK.dist_le_mul a ha b hb) (norm_nonneg c)

/-- Uniqueness for `y' = f(t) R(y)` on an open preconnected set of times. -/
theorem ode_uniq (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (I : Set ℝ) (hI : IsOpen I)
    (hIc : IsPreconnected I) (f : ℝ → ℝ) (hf : ContinuousOn f I) (y1 y2 : ℝ → V n)
    (h1 : ∀ t ∈ I, HasDerivAt y1 (f t • reeb H (y1 t)) t)
    (h2 : ∀ t ∈ I, HasDerivAt y2 (f t • reeb H (y2 t)) t)
    (hS : ∀ t ∈ I, y1 t ∈ energySurface H) (t0 : ℝ) (ht0 : t0 ∈ I) (heq : y1 t0 = y2 t0) :
    ∀ t ∈ I, y1 t = y2 t := by
  have hloc : ∀ t ∈ I, y1 t = y2 t → y1 =ᶠ[𝓝 t] y2 := by
    intro t ht he
    obtain ⟨K, N, hN, hK⟩ := (reeb_contDiffAt H hH (y1 t) (hS t ht)).exists_lipschitzOnWith
    have hfc : ContinuousAt f t := hf.continuousAt (hI.mem_nhds ht)
    have hfb : ∀ᶠ s in 𝓝 t, ‖f s‖₊ ≤ ‖f t‖₊ + 1 := by
      have := hfc.nnnorm.eventually (gt_mem_nhds (show ‖f t‖₊ < ‖f t‖₊ + 1 from lt_add_one _))
      filter_upwards [this] with s hs using hs.le
    refine ODE_solution_unique_of_eventually (K := (‖f t‖₊ + 1) * K)
      (v := fun s y => f s • reeb H y) (s := fun _ => N) ?_ ?_ ?_ he
    · filter_upwards [hfb] with s hs
      exact (lip_smul hK (f s)).weaken (mul_le_mul_of_nonneg_right hs K.2)
    · have hc := (h1 t ht).continuousAt
      filter_upwards [hI.mem_nhds ht, hc.preimage_mem_nhds hN] with s hs hs2
      exact ⟨h1 s hs, hs2⟩
    · have hc := (h2 t ht).continuousAt
      have hN2 : N ∈ 𝓝 (y2 t) := he ▸ hN
      filter_upwards [hI.mem_nhds ht, hc.preimage_mem_nhds hN2] with s hs hs2
      exact ⟨h2 s hs, hs2⟩
  set u := {t | y1 =ᶠ[𝓝 t] y2} with hu
  have huo : IsOpen u := isOpen_setOf_eventually_nhds
  have hsub : I ⊆ u := by
    refine hIc.subset_of_closure_inter_subset huo ⟨t0, ht0, hloc t0 ht0 heq⟩ ?_
    rintro t ⟨htc, ht⟩
    apply hloc t ht
    by_contra hne
    have hc := ((h1 t ht).continuousAt.sub (h2 t ht).continuousAt).eventually_ne
      (sub_ne_zero.mpr hne)
    obtain ⟨s, hs1, hs2⟩ := mem_closure_iff_nhds.mp htc _ hc
    exact hs1 (sub_eq_zero.mpr (hs2.self_of_nhds))
  intro t ht
  exact (hsub ht).self_of_nhds

/-- On a convex open set, a map with `dw = Im(G dz) R(w)` follows a Reeb trajectory `x`
through `w z₁`, reparametrized by a primitive `Θ` of `Im(G dz)`. -/
theorem local_eq (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n)
    (hx : ∀ τ, HasDerivAt x (reeb H (x τ)) τ) (B : Set ℂ) (hBo : IsOpen B) (hBc : Convex ℝ B)
    (w : ℂ → V n) (G : ℂ → ℂ) (hG : ContinuousOn G B) (hwd : ∀ z ∈ B, DifferentiableAt ℝ w z)
    (hdw : ∀ z ∈ B, ∀ v : ℂ, fderiv ℝ w z v = (G z * v).im • reeb H (w z))
    (hwS : ∀ z ∈ B, w z ∈ energySurface H) (Θ : ℂ → ℝ) (hΘd : ∀ z ∈ B, DifferentiableAt ℝ Θ z)
    (hdΘ : ∀ z ∈ B, ∀ v : ℂ, fderiv ℝ Θ z v = (G z * v).im) (z1 : ℂ) (hz1 : z1 ∈ B) (s1 : ℝ)
    (h1 : w z1 = x s1) : ∀ z ∈ B, w z = x (s1 + Θ z - Θ z1) := by
  intro z hz
  set σ : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap z1 z with hσ
  have hσa : ∀ s : ℝ, σ s = z1 + (s : ℂ) * (z - z1) := fun s => by
    rw [hσ, AffineMap.lineMap_apply_module']; rw [Complex.real_smul]; ring
  have hσd : ∀ s : ℝ, HasDerivAt σ (z - z1) s := by
    intro s
    have : (σ : ℝ → ℂ) = fun s : ℝ => z1 + (s : ℂ) * (z - z1) := funext hσa
    rw [this]
    have := ((hasDerivAt_id s).ofReal_comp.mul_const (z - z1)).const_add z1
    simpa using this
  set I := σ ⁻¹' B with hI
  have hIo : IsOpen I := hBo.preimage (AffineMap.lineMap_continuous)
  have hIc : IsPreconnected I := (hBc.affine_preimage σ).isPreconnected
  have h0 : (0:ℝ) ∈ I := by simp [hI, hσ, hz1]
  have h1I : (1:ℝ) ∈ I := by simp [hI, hσ, hz]
  set f : ℝ → ℝ := fun s => (G (σ s) * (z - z1)).im with hf
  have hfc : ContinuousOn f I := by
    have : ContinuousOn (fun s => G (σ s)) I :=
      hG.comp (AffineMap.lineMap_continuous).continuousOn (fun s hs => hs)
    exact Complex.continuous_im.comp_continuousOn (this.mul continuousOn_const)
  have := ode_uniq H hH I hIo hIc f hfc (fun s => w (σ s)) (fun s => x (s1 + Θ (σ s) - Θ z1))
    (fun s hs => by
      have := (hwd _ hs).hasFDerivAt.comp_hasDerivAt s (hσd s)
      rwa [hdw _ hs] at this)
    (fun s hs => by
      have hin : HasDerivAt (fun s => s1 + Θ (σ s) - Θ z1) (f s) s := by
        have := ((hΘd _ hs).hasFDerivAt.comp_hasDerivAt s (hσd s)).const_add s1
        have := this.sub_const (Θ z1)
        rwa [hdΘ _ hs] at this
      exact (hx _).scomp s hin)
    (fun s hs => hwS _ hs) 0 h0 (by simp [hσ, h1]) 1 h1I
  simpa [hσ] using this

end DR

end S_DR_d

-- ===== DR_b =====
section S_DR_b


open Set Metric Filter Topology

namespace DR

lemma exists_iso (Γ : Finset ℂ) (γ : ℂ) : ∃ r > 0, ∀ γ' ∈ Γ, γ' ≠ γ → r ≤ ‖γ' - γ‖ := by
  classical
  by_cases h : (Γ.erase γ).Nonempty
  · obtain ⟨m, hm, hmin⟩ := (Γ.erase γ).exists_min_image (fun γ' => ‖γ' - γ‖) h
    exact ⟨‖m - γ‖, norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hm)),
      fun γ' h1 h2 => hmin γ' (Finset.mem_erase.mpr ⟨h2, h1⟩)⟩
  · exact ⟨1, one_pos, fun γ' h1 h2 => absurd ⟨γ', Finset.mem_erase.mpr ⟨h2, h1⟩⟩ h⟩

lemma ball_punct_sub (Γ : Finset ℂ) (γ : ℂ) (r : ℝ) (hiso : ∀ γ' ∈ Γ, γ' ≠ γ → r ≤ ‖γ' - γ‖) :
    ∀ z ∈ ball γ r, z ≠ γ → z ∉ Γ := by
  intro z hz hne hzΓ
  have := hiso z hzΓ hne
  rw [mem_ball, dist_eq_norm] at hz
  linarith

/-- Residue at an isolated point where `|z - γ| |g z|` is bounded. -/
lemma residue (Γ : Finset ℂ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (↑Γ)ᶜ) (M : ℝ)
    (hb : ∀ z : ℂ, z ∉ Γ → ∀ s : ℝ, 0 < s → ball z s ⊆ (↑Γ)ᶜ → s * ‖g z‖ ≤ M) (γ : ℂ) :
    ∃ κ : ℂ, ∃ r > 0, ∃ Q : ℂ → ℂ, ContinuousAt Q γ ∧
      ∀ z ∈ ball γ r, z ≠ γ → g z = κ / (z - γ) + Q z := by
  obtain ⟨r, hr, hiso⟩ := exists_iso Γ γ
  set h := fun z => (z - γ) * g z with hh
  have hsub := ball_punct_sub Γ γ r hiso
  have hsub2 : ∀ z ∈ ball γ (r / 2), z ≠ γ → z ∉ Γ := fun z hz hne =>
    hsub z (ball_subset_ball (by linarith) hz) hne
  have hd : DifferentiableOn ℂ h (ball γ (r / 2) \ {γ}) :=
    (differentiableOn_id.sub_const γ).mul (hg.mono fun z hz => hsub2 z hz.1 hz.2)
  have hbd : BddAbove (norm ∘ h '' (ball γ (r / 2) \ {γ})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, ⟨hz, hne⟩, rfl⟩
    have hne' : z ≠ γ := hne
    have hpos : 0 < ‖z - γ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne')
    have hball : ball z ‖z - γ‖ ⊆ (↑Γ)ᶜ := by
      intro y hy hyΓ
      rw [mem_ball, dist_eq_norm] at hy hz
      by_cases hyγ : y = γ
      · subst hyγ; rw [norm_sub_rev] at hy; exact lt_irrefl _ hy
      · have h1 := hiso y hyΓ hyγ
        have h2 : ‖y - γ‖ ≤ ‖y - z‖ + ‖z - γ‖ := norm_sub_le_norm_sub_add_norm_sub y z γ
        linarith
    have := hb z (hsub2 z hz hne') _ hpos hball
    simpa [h, norm_mul] using this
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove
    (ball_mem_nhds γ (by linarith)) hd hbd
  set F := Function.update h γ (limUnder (𝓝[≠] γ) h) with hFdef
  have hFd : DifferentiableAt ℂ F γ :=
    (hF γ (mem_ball_self (by linarith))).differentiableAt (ball_mem_nhds γ (by linarith))
  refine ⟨F γ, r / 2, by linarith, dslope F γ, continuousAt_dslope_same.mpr hFd,
    fun z hz hne => ?_⟩
  rw [dslope_of_ne _ hne, slope_def_field]
  have : F z = (z - γ) * g z := by simp [hFdef, Function.update_of_ne hne, hh]
  rw [this]
  have hz : z - γ ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  ring

theorem partial_fractions (Γ : Finset ℂ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (↑Γ)ᶜ) (M : ℝ)
    (hb : ∀ z : ℂ, z ∉ Γ → ∀ s : ℝ, 0 < s → ball z s ⊆ (↑Γ)ᶜ → s * ‖g z‖ ≤ M) :
    ∃ κ : ℂ → ℂ, ∀ z : ℂ, z ∉ Γ → g z = ∑ γ ∈ Γ, κ γ / (z - γ) := by
  classical
  choose κ r hr Q hQ hgQ using residue Γ g hg M hb
  refine ⟨κ, ?_⟩
  set f : ℂ → ℂ := fun z => g z - ∑ γ ∈ Γ, κ γ / (z - γ) with hf
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  have hfd : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℂ f z := by
    intro z hz
    refine ((hg z hz).differentiableAt (hUo.mem_nhds hz)).sub ?_
    refine DifferentiableAt.fun_sum fun γ hγ => ?_
    refine (differentiableAt_const _).div (differentiableAt_id.sub_const γ) ?_
    exact sub_ne_zero.mpr (fun h => hz (h ▸ hγ))
  -- local form near γ ∈ Γ
  set L : ℂ → ℂ := fun γ => Q γ γ - ∑ γ' ∈ Γ.erase γ, κ γ' / (γ - γ') with hL
  have hlim : ∀ γ ∈ Γ, Tendsto f (𝓝[≠] γ) (𝓝 (L γ)) := by
    intro γ hγ
    have hc : ContinuousAt (fun z => Q γ z - ∑ γ' ∈ Γ.erase γ, κ γ' / (z - γ')) γ := by
      refine (hQ γ).sub (tendsto_finset_sum _ fun γ' hγ' => ?_)
      refine continuousAt_const.div (continuousAt_id.sub continuousAt_const) ?_
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hγ').symm
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hm : {γ}ᶜ ∩ ball γ (r γ) ∈ 𝓝[≠] γ :=
      inter_mem_nhdsWithin _ (ball_mem_nhds γ (hr γ))
    filter_upwards [hm] with z hz
    obtain ⟨hz2, hz1⟩ := hz
    have hne : z ≠ γ := hz2
    simp only [hf]
    rw [hgQ γ z hz1 hne, ← Finset.add_sum_erase Γ _ hγ]
    ring
  set F : ℂ → ℂ := fun z => if z ∈ Γ then L z else f z with hF
  have hFeq : ∀ z : ℂ, z ∉ Γ → F z = f z := fun z hz => by simp [hF, hz]
  have hFd' : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℂ F z := by
    intro z hz
    refine (hfd z hz).congr_of_eventuallyEq ?_
    filter_upwards [hUo.mem_nhds hz] with y hy
    exact hFeq y hy
  have hFd : Differentiable ℂ F := by
    intro z
    by_cases hz : z ∈ Γ
    · obtain ⟨ρ, hρ, hiso⟩ := exists_iso Γ z
      have hsub := ball_punct_sub Γ z ρ hiso
      have hs : ball z ρ ∈ 𝓝 z := ball_mem_nhds z hρ
      refine ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp ⟨?_, ?_⟩).differentiableAt hs
      · intro y hy
        exact (hFd' y (hsub y hy.1 hy.2)).differentiableWithinAt
      · rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
        have hFz : F z = L z := by simp [hF, hz]
        rw [hFz]
        refine (hlim z hz).congr' ?_
        have hm : {z}ᶜ ∩ ball z ρ ∈ 𝓝[≠] z := inter_mem_nhdsWithin _ hs
        filter_upwards [hm] with y hy
        exact (hFeq y (hsub y hy.2 hy.1)).symm
    · exact hFd' z hz
  -- decay at infinity
  set R0 : ℝ := 1 + ∑ γ ∈ Γ, ‖γ‖ with hR0
  have hR0γ : ∀ γ ∈ Γ, ‖γ‖ < R0 := fun γ hγ => by
    have := Finset.single_le_sum (f := fun γ => ‖γ‖) (fun _ _ => norm_nonneg _) hγ
    linarith
  have hR0pos : 0 < R0 := by
    have : 0 ≤ ∑ γ ∈ Γ, ‖γ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set C : ℝ := 2 * |M| + 2 * ∑ γ ∈ Γ, ‖κ γ‖ with hC
  have hdecay : ∀ z : ℂ, 2 * R0 ≤ ‖z‖ → ‖F z‖ ≤ C / ‖z‖ := by
    intro z hz
    have hzpos : 0 < ‖z‖ := by linarith
    have hzΓ : z ∉ Γ := fun h => by have := hR0γ z h; linarith
    rw [hFeq z hzΓ]
    have hball : ball z (‖z‖ / 2) ⊆ (↑Γ)ᶜ := by
      intro y hy hyΓ
      have h1 := hR0γ y hyΓ
      rw [mem_ball, dist_eq_norm] at hy
      have h2 : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := norm_le_norm_sub_add z y
      rw [norm_sub_rev] at h2
      linarith
    have hg1 := hb z hzΓ (‖z‖ / 2) (by positivity) hball
    have hg2 : ‖g z‖ ≤ 2 * |M| / ‖z‖ := by
      rw [le_div_iff₀ hzpos]; have := le_abs_self M; nlinarith
    have hterm : ∀ γ ∈ Γ, ‖κ γ / (z - γ)‖ ≤ 2 * ‖κ γ‖ / ‖z‖ := by
      intro γ hγ
      have h1 := hR0γ γ hγ
      have h2 : ‖z‖ - ‖γ‖ ≤ ‖z - γ‖ := norm_sub_norm_le z γ
      have h3 : ‖z‖ / 2 ≤ ‖z - γ‖ := by linarith
      rw [norm_div, div_le_div_iff₀ (by linarith) hzpos]
      have := norm_nonneg (κ γ)
      nlinarith
    calc ‖g z - ∑ γ ∈ Γ, κ γ / (z - γ)‖ ≤ ‖g z‖ + ‖∑ γ ∈ Γ, κ γ / (z - γ)‖ := norm_sub_le _ _
      _ ≤ 2 * |M| / ‖z‖ + ∑ γ ∈ Γ, 2 * ‖κ γ‖ / ‖z‖ :=
          add_le_add hg2 ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
      _ = C / ‖z‖ := by rw [hC, ← Finset.sum_div, ← Finset.mul_sum]; ring
  have hCnn : 0 ≤ C := by
    have : 0 ≤ ∑ γ ∈ Γ, ‖κ γ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have := abs_nonneg M
    linarith
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0:ℂ) (2 * R0)).exists_bound_of_continuousOn
    hFd.continuous.continuousOn
  have hFb : Bornology.IsBounded (range F) := by
    refine (isBounded_closedBall (x := (0:ℂ)) (r := max B (C / (2 * R0)))).subset ?_
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    by_cases hz : ‖z‖ ≤ 2 * R0
    · exact (hB z (by rwa [mem_closedBall, dist_zero_right])).trans (le_max_left _ _)
    · push_neg at hz
      refine (hdecay z hz.le).trans ((div_le_div_of_nonneg_left hCnn (by positivity) hz.le).trans
        (le_max_right _ _))
  have hF0 : ∀ z, F z = 0 := by
    intro z
    refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
    set N : ℝ := 2 * R0 + C / ε with hN
    have hNpos : 0 < N := by positivity
    have hCe : 0 ≤ C / ε := by positivity
    have h1 := hFd.apply_eq_apply_of_bounded hFb z (N : ℂ)
    have h2 := hdecay (N : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]; linarith)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos] at h2
    rw [h1, zero_add]
    refine h2.trans ?_
    rw [div_le_iff₀ hNpos]
    have : C ≤ ε * (C / ε) := by rw [mul_div_cancel₀ _ hε.ne']
    nlinarith
  intro z hz
  have := hF0 z
  rw [hFeq z hz] at this
  simp only [hf] at this
  exact sub_eq_zero.mp this

end DR

end S_DR_b

-- ===== DR_c =====
section S_DR_c


open Set Metric Filter Topology

namespace DR

lemma compl_conn (Γ : Finset ℂ) : IsPreconnected ((↑Γ)ᶜ : Set ℂ) :=
  (Γ.finite_toSet.countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

lemma compl_open (Γ : Finset ℂ) : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl

/-- The residues are real: going once around `γ`, `a` returns to its value. -/
theorem kappa_real (Γ : Finset ℂ) (a : ℂ → ℝ) (ha : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ a z)
    (κ : ℂ → ℂ)
    (hda : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ a z v = ((∑ γ ∈ Γ, κ γ / (z - γ)) * v).re) :
    ∀ γ ∈ Γ, (κ γ).im = 0 := by
  classical
  intro γ hγ
  obtain ⟨r, hr, hiso⟩ := exists_iso Γ γ
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  set c : ℝ → ℂ := fun θ => γ + ρ * Complex.exp (θ * Complex.I) with hc
  have hcγ : ∀ θ : ℝ, c θ - γ = ρ * Complex.exp (θ * Complex.I) := fun θ => by simp [hc]
  have hcn : ∀ θ : ℝ, ‖c θ - γ‖ = ρ := fun θ => by
    rw [hcγ, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρpos]
  have hcne : ∀ θ : ℝ, c θ ≠ γ := fun θ h => by
    have := hcn θ; rw [h, sub_self, norm_zero] at this; linarith
  have hcΓ : ∀ θ : ℝ, c θ ∉ Γ := fun θ => ball_punct_sub Γ γ r hiso (c θ)
    (by rw [mem_ball, dist_eq_norm, hcn θ]; linarith) (hcne θ)
  have hcd : ∀ θ : ℝ, HasDerivAt c (Complex.I * (c θ - γ)) θ := by
    intro θ
    have h1 := ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp
    have h2 := (h1.const_mul (ρ : ℂ)).const_add γ
    refine (h2 : HasDerivAt c _ θ).congr_deriv ?_
    rw [hcγ]; simp; ring
  -- the other punctures: local logarithms
  have hq : ∀ γ' ∈ Γ.erase γ, ∀ θ : ℝ, (c θ - γ') / (γ - γ') ∈ Complex.slitPlane := by
    intro γ' hγ' θ
    have hne : γ' ≠ γ := Finset.ne_of_mem_erase hγ'
    have hγ'Γ := Finset.mem_of_mem_erase hγ'
    have hd : r ≤ ‖γ - γ'‖ := by rw [norm_sub_rev]; exact hiso γ' hγ'Γ hne
    have hd0 : γ - γ' ≠ 0 := sub_ne_zero.mpr hne.symm
    have heq : (c θ - γ') / (γ - γ') = 1 + (c θ - γ) / (γ - γ') := by field_simp; ring
    rw [heq, Complex.mem_slitPlane_iff]
    left
    have h1 : ‖(c θ - γ) / (γ - γ')‖ ≤ 1 / 2 := by
      rw [norm_div, hcn, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h2 := Complex.abs_re_le_norm ((c θ - γ) / (γ - γ'))
    rw [Complex.add_re, Complex.one_re]
    have := neg_abs_le ((c θ - γ) / (γ - γ')).re
    linarith
  set Φ : ℝ → ℝ := fun θ => a (c θ) + (κ γ).im * θ -
    ∑ γ' ∈ Γ.erase γ, (κ γ' * Complex.log ((c θ - γ') / (γ - γ'))).re with hΦ
  have hΦd : ∀ θ, HasDerivAt Φ 0 θ := by
    intro θ
    have hA := (ha _ (hcΓ θ)).hasFDerivAt.comp_hasDerivAt θ (hcd θ)
    have hL : ∀ γ' ∈ Γ.erase γ, HasDerivAt
        (fun θ => (κ γ' * Complex.log ((c θ - γ') / (γ - γ'))).re)
        ((κ γ' * (Complex.I * (c θ - γ) / (c θ - γ'))).re) θ := by
      intro γ' hγ'
      have hne : γ' ≠ γ := Finset.ne_of_mem_erase hγ'
      have hd0 : γ - γ' ≠ 0 := sub_ne_zero.mpr hne.symm
      have hc0 : c θ - γ' ≠ 0 := sub_ne_zero.mpr
        (fun h => hcΓ θ (h ▸ Finset.mem_of_mem_erase hγ'))
      have h1 := (((hcd θ).sub_const γ').div_const (γ - γ')).clog_real (hq γ' hγ' θ)
      have h2 := (h1.const_mul (κ γ'))
      have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ h2
      have h4 : HasDerivAt (fun θ => (κ γ' * Complex.log ((c θ - γ') / (γ - γ'))).re)
          ((κ γ' * (Complex.I * (c θ - γ) / (γ - γ') / ((c θ - γ') / (γ - γ')))).re) θ := h3
      refine h4.congr_deriv ?_
      congr 2
      field_simp
    have hS := HasDerivAt.fun_sum hL
    have hT := (hA.add ((hasDerivAt_id θ).const_mul (κ γ).im)).sub hS
    refine hT.congr_deriv ?_
    rw [hda _ (hcΓ θ), ← Finset.add_sum_erase Γ _ hγ, add_mul, Complex.add_re, Finset.sum_mul,
      Complex.re_sum]
    have hI : (κ γ / (c θ - γ) * (Complex.I * (c θ - γ))).re = -(κ γ).im := by
      have : c θ - γ ≠ 0 := sub_ne_zero.mpr (hcne θ)
      rw [show κ γ / (c θ - γ) * (Complex.I * (c θ - γ)) = κ γ * Complex.I by field_simp]
      simp
    rw [hI]
    have : ∀ γ' ∈ Γ.erase γ, (κ γ' / (c θ - γ') * (Complex.I * (c θ - γ))).re =
        (κ γ' * (Complex.I * (c θ - γ) / (c θ - γ'))).re := fun γ' _ => by ring_nf
    rw [Finset.sum_congr rfl this]
    simp
  have hconst := is_const_of_deriv_eq_zero (fun θ => (hΦd θ).differentiableAt)
    (fun θ => (hΦd θ).deriv) (2 * Real.pi) 0
  have hc2 : c (2 * Real.pi) = c 0 := by
    simp only [hc]
    congr 2
    push_cast
    rw [Complex.exp_two_pi_mul_I, zero_mul, Complex.exp_zero]
  simp only [hΦ, hc2] at hconst
  have := Real.pi_pos
  nlinarith

lemma hasFDerivAt_logsq (γ z : ℂ) (hz : z ≠ γ) :
    HasFDerivAt (fun z : ℂ => Real.log (‖z - γ‖ ^ 2))
      ((‖z - γ‖ ^ 2)⁻¹ • ((2 • innerSL ℝ (z - γ)).comp (ContinuousLinearMap.id ℝ ℂ))) z := by
  have h1 := (hasStrictFDerivAt_norm_sq (z - γ)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const γ)
  have h2 := h1.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))
  exact h2

/-- `a = Σ κ_γ log |z - γ| + c₀` on `ℂ \ Γ`. -/
theorem a_eq (Γ : Finset ℂ) (a : ℂ → ℝ) (ha : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ a z)
    (k : ℂ → ℝ)
    (hda : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ a z v = ((∑ γ ∈ Γ, (k γ : ℂ) / (z - γ)) * v).re) :
    ∃ c0 : ℝ, ∀ z : ℂ, z ∉ Γ → a z = ∑ γ ∈ Γ, k γ * Real.log ‖z - γ‖ + c0 := by
  classical
  set A : ℂ → ℝ := fun z => a z - ∑ γ ∈ Γ, k γ / 2 * Real.log (‖z - γ‖ ^ 2) with hA
  have hAd : ∀ z ∈ ((↑Γ)ᶜ : Set ℂ), HasFDerivAt A (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have hz' : z ∉ Γ := hz
    have hne : ∀ γ ∈ Γ, z ≠ γ := fun γ hγ h => hz' (h ▸ hγ)
    have hS := HasFDerivAt.fun_sum (u := Γ)
      (fun γ hγ => (hasFDerivAt_logsq γ z (hne γ hγ)).const_mul (k γ / 2))
    refine ((ha z hz').hasFDerivAt.sub hS).congr_fderiv ?_
    ext1 v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, hda z hz' v, Finset.sum_mul,
      Complex.re_sum]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hzγ : z - γ ≠ 0 := sub_ne_zero.mpr (hne γ hγ)
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq]
    have hn : Complex.normSq (z - γ) ≠ 0 := (Complex.normSq_pos.mpr hzγ).ne'
    rw [div_mul_eq_mul_div, Complex.div_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, nsmul_eq_mul, Complex.sub_re, Complex.sub_im]
    rw [Complex.normSq_apply] at hn ⊢
    simp only [Complex.sub_re, Complex.sub_im] at hn ⊢
    field_simp
    ring
  obtain ⟨z0, hz0⟩ : ∃ z0 : ℂ, z0 ∉ Γ := by
    by_contra h; push Not at h
    exact (Set.infinite_univ (α := ℂ)) (Γ.finite_toSet.subset fun z _ => h z)
  refine ⟨A z0, fun z hz => ?_⟩
  have := (compl_open Γ).is_const_of_fderiv_eq_zero (𝕜 := ℝ) (compl_conn Γ)
    (fun y hy => (hAd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hAd y hy).fderiv) (show z ∈ ((↑Γ)ᶜ : Set ℂ) from hz)
    (show z0 ∈ ((↑Γ)ᶜ : Set ℂ) from hz0)
  rw [← this]
  simp only [hA]
  have : ∀ γ ∈ Γ, k γ / 2 * Real.log (‖z - γ‖ ^ 2) = k γ * Real.log ‖z - γ‖ := fun γ _ => by
    rw [Real.log_pow]; push_cast; ring
  rw [Finset.sum_congr rfl this]
  ring

/-- Negative punctures force positive residues. -/
theorem kappa_pos (Γ : Finset ℂ) (a : ℂ → ℝ) (k : ℂ → ℝ) (c0 : ℝ)
    (haeq : ∀ z : ℂ, z ∉ Γ → a z = ∑ γ ∈ Γ, k γ * Real.log ‖z - γ‖ + c0)
    (γ : ℂ) (hγ : γ ∈ Γ) (hneg : Tendsto a (𝓝[≠] γ) atBot) : 0 < k γ := by
  classical
  by_contra hle
  push Not at hle
  obtain ⟨r, hr, hiso⟩ := exists_iso Γ γ
  set B : ℂ → ℝ := fun z => ∑ γ' ∈ Γ.erase γ, k γ' * Real.log ‖z - γ'‖ with hB
  have hBc : ContinuousAt B γ := by
    refine tendsto_finset_sum _ fun γ' hγ' => ?_
    have hne : γ - γ' ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hγ').symm
    exact continuousAt_const.mul
      ((continuousAt_id.sub continuousAt_const).norm.log (norm_ne_zero_iff.mpr hne))
  have hev1 : ∀ᶠ z in 𝓝[≠] γ, B γ - 1 < B z :=
    (hBc.eventually (lt_mem_nhds (by linarith : B γ - 1 < B γ))).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ z in 𝓝[≠] γ, z ∈ ball γ (min r 1) ∧ z ≠ γ :=
    inter_mem_nhdsWithin _ (ball_mem_nhds γ (lt_min hr one_pos)) |> fun h => by
      filter_upwards [h] with z hz; exact ⟨hz.2, hz.1⟩
  have hev3 : ∀ᶠ z in 𝓝[≠] γ, a z < B γ - 1 + c0 := hneg.eventually (eventually_lt_atBot _)
  obtain ⟨z, h1, ⟨hzb, hzne⟩, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have hzΓ : z ∉ Γ := ball_punct_sub Γ γ r hiso z (ball_subset_ball (min_le_left _ _) hzb) hzne
  rw [haeq z hzΓ, ← Finset.add_sum_erase Γ _ hγ] at h3
  have hlog : Real.log ‖z - γ‖ ≤ 0 := by
    apply Real.log_nonpos (norm_nonneg _)
    rw [mem_ball, dist_eq_norm] at hzb
    exact (hzb.trans_le (min_le_right _ _)).le
  have : 0 ≤ k γ * Real.log ‖z - γ‖ := mul_nonneg_of_nonpos_of_nonpos hle hlog
  simp only [hB] at h1
  linarith

end DR

end S_DR_c

-- ===== DR_e =====
section S_DR_e


open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace DR

open DP

noncomputable def cl (γ : ℂ) (ρ : ℝ) (θ : ℝ) : ℂ := γ + ρ * Complex.exp (θ * Complex.I)

noncomputable def phase (Γ : Finset ℂ) (k : ℂ → ℝ) (γ : ℂ) (ρ : ℝ) (θ : ℝ) : ℝ :=
  k γ * θ + ∑ γ' ∈ Γ.erase γ, k γ' * (Complex.log ((cl γ ρ θ - γ') / (γ - γ'))).im

noncomputable def Gk (Γ : Finset ℂ) (k : ℂ → ℝ) (z : ℂ) : ℂ := ∑ γ' ∈ Γ, (k γ' : ℂ) / (z - γ')

section loop

variable (Γ : Finset ℂ) (k : ℂ → ℝ) (γ : ℂ) (hγ : γ ∈ Γ) (r : ℝ) (hr : 0 < r)
  (hiso : ∀ γ' ∈ Γ, γ' ≠ γ → r ≤ ‖γ' - γ‖) (ρ : ℝ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r / 2)

include hρ0 in
lemma cl_sub_norm (θ : ℝ) : ‖cl γ ρ θ - γ‖ = ρ := by
  simp only [cl, add_sub_cancel_left]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ0]

include hρ0 in
lemma cl_ne (θ : ℝ) : cl γ ρ θ ≠ γ := fun h => by
  have := cl_sub_norm γ ρ hρ0 θ; rw [h, sub_self, norm_zero] at this; linarith

include hr hiso hρ0 hρr in
lemma cl_notMem (θ : ℝ) : cl γ ρ θ ∉ Γ :=
  ball_punct_sub Γ γ r hiso _ (by rw [mem_ball, dist_eq_norm, cl_sub_norm γ ρ hρ0]; linarith)
    (cl_ne γ ρ hρ0 θ)

include hr hiso hρ0 hρr in
lemma cl_far (γ' : ℂ) (hγ' : γ' ∈ Γ.erase γ) (θ : ℝ) : r / 2 ≤ ‖cl γ ρ θ - γ'‖ := by
  have hd : r ≤ ‖γ' - γ‖ := hiso γ' (Finset.mem_of_mem_erase hγ') (Finset.ne_of_mem_erase hγ')
  have h1 : ‖γ' - γ‖ ≤ ‖γ' - cl γ ρ θ‖ + ‖cl γ ρ θ - γ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [cl_sub_norm γ ρ hρ0, norm_sub_rev γ' (cl γ ρ θ)] at h1
  linarith

lemma cl_hasDerivAt (θ : ℝ) : HasDerivAt (cl γ ρ) (Complex.I * (cl γ ρ θ - γ)) θ := by
  have h1 := ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp
  have h2 := (h1.const_mul (ρ : ℂ)).const_add γ
  refine (h2 : HasDerivAt (cl γ ρ) _ θ).congr_deriv ?_
  simp [cl]; ring

lemma cl_periodic (θ : ℝ) : cl γ ρ (θ + 2 * Real.pi) = cl γ ρ θ := by
  simp only [cl]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add, mul_comm (2 * (Real.pi : ℂ)) Complex.I,
    show Complex.I * (2 * Real.pi) = 2 * Real.pi * Complex.I by ring, Complex.exp_two_pi_mul_I,
    mul_one]

include hr hiso hρ0 hρr in
lemma cl_slit (γ' : ℂ) (hγ' : γ' ∈ Γ.erase γ) (θ : ℝ) :
    (cl γ ρ θ - γ') / (γ - γ') ∈ Complex.slitPlane := by
  have hne : γ' ≠ γ := Finset.ne_of_mem_erase hγ'
  have hd : r ≤ ‖γ - γ'‖ := by rw [norm_sub_rev]; exact hiso γ' (Finset.mem_of_mem_erase hγ') hne
  have hd0 : γ - γ' ≠ 0 := sub_ne_zero.mpr hne.symm
  have heq : (cl γ ρ θ - γ') / (γ - γ') = 1 + (cl γ ρ θ - γ) / (γ - γ') := by field_simp; ring
  rw [heq, Complex.mem_slitPlane_iff]
  left
  have h1 : ‖(cl γ ρ θ - γ) / (γ - γ')‖ ≤ 1 / 2 := by
    rw [norm_div, cl_sub_norm γ ρ hρ0, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h2 := Complex.abs_re_le_norm ((cl γ ρ θ - γ) / (γ - γ'))
  rw [Complex.add_re, Complex.one_re]
  have := neg_abs_le ((cl γ ρ θ - γ) / (γ - γ')).re
  linarith

include hγ hr hiso hρ0 hρr in
lemma phase_hasDerivAt (θ : ℝ) :
    HasDerivAt (phase Γ k γ ρ) ((Gk Γ k (cl γ ρ θ) * (Complex.I * (cl γ ρ θ - γ))).im) θ := by
  classical
  have hL : ∀ γ' ∈ Γ.erase γ, HasDerivAt
      (fun θ => k γ' * (Complex.log ((cl γ ρ θ - γ') / (γ - γ'))).im)
      (k γ' * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im) θ := by
    intro γ' hγ'
    have hne : γ' ≠ γ := Finset.ne_of_mem_erase hγ'
    have hd0 : γ - γ' ≠ 0 := sub_ne_zero.mpr hne.symm
    have hc0 : cl γ ρ θ - γ' ≠ 0 := sub_ne_zero.mpr
      (fun h => cl_notMem Γ γ r hr hiso ρ hρ0 hρr θ (h ▸ Finset.mem_of_mem_erase hγ'))
    have h1 := (((cl_hasDerivAt γ ρ θ).sub_const γ').div_const (γ - γ')).clog_real
      (cl_slit Γ γ r hr hiso ρ hρ0 hρr γ' hγ' θ)
    have h3 := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ h1).const_mul (k γ')
    have h4 : HasDerivAt (fun θ => k γ' * (Complex.log ((cl γ ρ θ - γ') / (γ - γ'))).im)
        (k γ' * (Complex.I * (cl γ ρ θ - γ) / (γ - γ') / ((cl γ ρ θ - γ') / (γ - γ'))).im) θ := h3
    refine h4.congr_deriv ?_
    rw [show Complex.I * (cl γ ρ θ - γ) / (γ - γ') / ((cl γ ρ θ - γ') / (γ - γ')) =
      Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ') by field_simp]
  have hT := ((hasDerivAt_id θ).const_mul (k γ)).add (HasDerivAt.fun_sum hL)
  refine (hT : HasDerivAt (phase Γ k γ ρ) _ θ).congr_deriv ?_
  rw [Gk, ← Finset.add_sum_erase Γ _ hγ, add_mul, Complex.add_im, Finset.sum_mul, Complex.im_sum]
  have hI : ((k γ : ℂ) / (cl γ ρ θ - γ) * (Complex.I * (cl γ ρ θ - γ))).im = k γ := by
    have : cl γ ρ θ - γ ≠ 0 := sub_ne_zero.mpr (cl_ne γ ρ hρ0 θ)
    rw [show (k γ : ℂ) / (cl γ ρ θ - γ) * (Complex.I * (cl γ ρ θ - γ)) = (k γ : ℂ) * Complex.I by
      field_simp]
    simp
  rw [hI]
  simp only [id, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun γ' _ => ?_
  rw [show (k γ' : ℂ) / (cl γ ρ θ - γ') * (Complex.I * (cl γ ρ θ - γ)) =
    (k γ' : ℂ) * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')) by ring, Complex.im_ofReal_mul]

lemma phase_periodic (θ : ℝ) : phase Γ k γ ρ (θ + 2 * Real.pi) = phase Γ k γ ρ θ + 2 * Real.pi * k γ := by
  simp only [phase, cl_periodic]
  ring

include hr hiso hρ0 hρr in
lemma phase_deriv_ge (hρs : 4 * ρ * ∑ γ' ∈ Γ.erase γ, |k γ'| ≤ r * k γ) (θ : ℝ) :
    k γ / 2 ≤ k γ + ∑ γ' ∈ Γ.erase γ, k γ' * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im := by
  have hb : ∀ γ' ∈ Γ.erase γ, -(|k γ'| * (2 * ρ / r)) ≤
      k γ' * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im := by
    intro γ' hγ'
    have hf := cl_far Γ γ r hr hiso ρ hρ0 hρr γ' hγ' θ
    have h1 : |(Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im| ≤ 2 * ρ / r := by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, cl_sub_norm γ ρ hρ0,
        div_le_div_iff₀ (by linarith) hr]
      nlinarith
    have h2 := abs_mul (k γ') ((Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im)
    have h3 := neg_abs_le (k γ' * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im)
    have h4 : |k γ'| * |(Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im| ≤ |k γ'| * (2 * ρ / r) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  have hs := Finset.sum_le_sum hb
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul] at hs
  have : (∑ γ' ∈ Γ.erase γ, |k γ'|) * (2 * ρ / r) ≤ k γ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hr (by norm_num)]; nlinarith
  linarith

include hγ hr hiso hρ0 hρr in
lemma Gk_im_eq (θ : ℝ) : (Gk Γ k (cl γ ρ θ) * (Complex.I * (cl γ ρ θ - γ))).im =
    k γ + ∑ γ' ∈ Γ.erase γ, k γ' * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')).im := by
  classical
  rw [Gk, ← Finset.add_sum_erase Γ _ hγ, add_mul, Complex.add_im, Finset.sum_mul, Complex.im_sum]
  have hI : ((k γ : ℂ) / (cl γ ρ θ - γ) * (Complex.I * (cl γ ρ θ - γ))).im = k γ := by
    have : cl γ ρ θ - γ ≠ 0 := sub_ne_zero.mpr (cl_ne γ ρ hρ0 θ)
    rw [show (k γ : ℂ) / (cl γ ρ θ - γ) * (Complex.I * (cl γ ρ θ - γ)) = (k γ : ℂ) * Complex.I by
      field_simp]
    simp
  rw [hI]
  congr 1
  refine Finset.sum_congr rfl fun γ' _ => ?_
  rw [show (k γ' : ℂ) / (cl γ ρ θ - γ') * (Complex.I * (cl γ ρ θ - γ)) =
    (k γ' : ℂ) * (Complex.I * (cl γ ρ θ - γ) / (cl γ ρ θ - γ')) by ring, Complex.im_ofReal_mul]

end loop

end DR

end S_DR_e

-- ===== DR_f =====
section S_DR_f


open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace DR

open DP

variable {n : ℕ}

/-- A loop around a puncture with positive residue yields a periodic Reeb orbit through `w`. -/
theorem exists_orbit (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Γ : Finset ℂ) (k : ℂ → ℝ)
    (γ : ℂ) (hγ : γ ∈ Γ) (hk : 0 < k γ) (w : ℂ → V n)
    (hwd : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ w z)
    (hdw : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ w z v = (Gk Γ k z * v).im • reeb H (w z))
    (hwS : ∀ z : ℂ, z ∉ Γ → w z ∈ energySurface H) :
    ∃ P : ReebOrbit H, P.T = 2 * Real.pi * k γ ∧ ∃ z0 : ℂ, z0 ∉ Γ ∧ ∃ s0 : ℝ, w z0 = P.x s0 := by
  classical
  obtain ⟨r, hr, hiso⟩ := exists_iso Γ γ
  set S := ∑ γ' ∈ Γ.erase γ, |k γ'| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set ρ := min (r / 2) (r * k γ / (4 * (S + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρr : ρ ≤ r / 2 := min_le_left _ _
  have hρs : 4 * ρ * S ≤ r * k γ := by
    have h1 : ρ ≤ r * k γ / (4 * (S + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [mul_pos hr hk]
  set Θ := phase Γ k γ ρ with hΘdef
  set D : ℝ → ℝ := fun θ => (Gk Γ k (cl γ ρ θ) * (Complex.I * (cl γ ρ θ - γ))).im with hD
  have hΘ : ∀ θ, HasDerivAt Θ (D θ) θ := phase_hasDerivAt Γ k γ hγ r hr hiso ρ hρ0 hρr
  have hDge : ∀ θ, k γ / 2 ≤ D θ := fun θ => by
    simp only [hD]
    rw [Gk_im_eq Γ k γ hγ r hr hiso ρ hρ0 hρr θ]
    exact phase_deriv_ge Γ k γ r hr hiso ρ hρ0 hρr hρs θ
  have hDpos : ∀ θ, 0 < D θ := fun θ => by linarith [hDge θ]
  have hΘc : Continuous Θ := continuous_iff_continuousAt.mpr fun θ => (hΘ θ).continuousAt
  have hmono : StrictMono Θ := strictMono_of_deriv_pos fun θ => by rw [(hΘ θ).deriv]; exact hDpos θ
  have hmono2 : Monotone fun θ => Θ θ - k γ / 2 * θ := by
    refine monotone_of_deriv_nonneg (fun θ => ((hΘ θ).sub ((hasDerivAt_id θ).const_mul _)).differentiableAt)
      fun θ => ?_
    have h := (hΘ θ).sub ((hasDerivAt_id θ).const_mul (k γ / 2))
    have h' : HasDerivAt (fun θ => Θ θ - k γ / 2 * θ) (D θ - k γ / 2 * 1) θ := h
    rw [h'.deriv]
    linarith [hDge θ]
  have hsurj : Function.Surjective Θ := by
    refine hΘc.surjective ?_ ?_
    · refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left _ (Θ 0)
        ((tendsto_id).const_mul_atTop (by linarith : 0 < k γ / 2)))
      filter_upwards [eventually_ge_atTop 0] with θ hθ
      have := hmono2 hθ
      simp only [mul_zero, sub_zero] at this
      simp only [id]; linarith
    · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_left _ (Θ 0)
        ((tendsto_id).const_mul_atBot (by linarith : 0 < k γ / 2)))
      filter_upwards [eventually_le_atBot 0] with θ hθ
      have := hmono2 hθ
      simp only [mul_zero, sub_zero] at this
      simp only [id]; linarith
  set e := StrictMono.orderIsoOfSurjective Θ hmono hsurj with he
  set ψ : ℝ → ℝ := fun τ => e.symm τ with hψ
  have hψc : Continuous ψ := e.symm.continuous
  have hΘψ : ∀ τ, Θ (ψ τ) = τ := fun τ => e.apply_symm_apply τ
  have hψΘ : ∀ θ, ψ (Θ θ) = θ := fun θ => e.symm_apply_apply θ
  have hψd : ∀ τ, HasDerivAt ψ (D (ψ τ))⁻¹ τ := fun τ =>
    HasDerivAt.of_local_left_inverse hψc.continuousAt (hΘ (ψ τ)) (hDpos _).ne'
      (Eventually.of_forall hΘψ)
  have hy : ∀ θ, HasDerivAt (fun θ => w (cl γ ρ θ)) (D θ • reeb H (w (cl γ ρ θ))) θ := by
    intro θ
    have hm := cl_notMem Γ γ r hr hiso ρ hρ0 hρr θ
    have := (hwd _ hm).hasFDerivAt.comp_hasDerivAt θ (cl_hasDerivAt γ ρ θ)
    rwa [hdw _ hm] at this
  have hper : ∀ τ, ψ (τ + 2 * Real.pi * k γ) = ψ τ + 2 * Real.pi := by
    intro τ
    have : Θ (ψ τ + 2 * Real.pi) = τ + 2 * Real.pi * k γ := by
      rw [hΘdef, phase_periodic, ← hΘdef, hΘψ]
    rw [← this, hψΘ]
  let P : ReebOrbit H :=
    { x := fun τ => w (cl γ ρ (ψ τ))
      T := 2 * Real.pi * k γ
      T_pos := by positivity
      mem := fun τ => hwS _ (cl_notMem Γ γ r hr hiso ρ hρ0 hρr _)
      hasDerivAt := fun τ => by
        have := (hy (ψ τ)).scomp τ (hψd τ)
        refine (this : HasDerivAt (fun τ => w (cl γ ρ (ψ τ))) _ τ).congr_deriv ?_
        rw [smul_smul, inv_mul_cancel₀ (hDpos _).ne', one_smul]
      periodic := fun τ => by
        show w (cl γ ρ (ψ (τ + 2 * Real.pi * k γ))) = w (cl γ ρ (ψ τ))
        rw [hper, cl_periodic] }
  refine ⟨P, rfl, cl γ ρ 0, cl_notMem Γ γ r hr hiso ρ hρ0 hρr 0, Θ 0, ?_⟩
  show w (cl γ ρ 0) = w (cl γ ρ (ψ (Θ 0)))
  rw [hψΘ]

end DR

end S_DR_f

-- ===== DR_g =====
section S_DR_g


open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace DR

open DP

variable {n : ℕ}

lemma exists_eps (Γ : Finset ℂ) (z1 : ℂ) (hz1 : z1 ∉ Γ) : ∃ ε > 0, ∀ γ ∈ Γ, ε ≤ ‖z1 - γ‖ := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (compl_open Γ) z1 hz1
  refine ⟨ε, hε, fun γ hγ => ?_⟩
  by_contra h
  push Not at h
  have : γ ∈ ball z1 ε := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact h
  exact hb this hγ

lemma ball_notMem (Γ : Finset ℂ) (z1 : ℂ) (ε : ℝ) (hε : ∀ γ ∈ Γ, ε ≤ ‖z1 - γ‖) (z : ℂ)
    (hz : z ∈ ball z1 ε) : z ∉ Γ := by
  intro hzΓ
  have h1 := hε z hzΓ
  rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
  linarith

/-- Propagation along the connected set `ℂ \ Γ`. -/
lemma propagate (Γ : Finset ℂ) (Q : ℂ → Prop)
    (hball : ∀ z1 : ℂ, z1 ∉ Γ → ∃ ε > 0, ∀ z2 ∈ ball z1 ε, z2 ∉ Γ → Q z2 →
      ∀ z ∈ ball z1 ε, z ∉ Γ → Q z)
    (z0 : ℂ) (hz0 : z0 ∉ Γ) (hQ0 : Q z0) : ∀ z : ℂ, z ∉ Γ → Q z := by
  classical
  choose! ε hε hQ using hball
  set U : Set ℂ := (↑Γ)ᶜ with hU
  set u : Set ℂ := U ∩ ⋃ z1 ∈ {z1 | z1 ∉ Γ ∧ ∃ z2 ∈ ball z1 (ε z1), z2 ∉ Γ ∧ Q z2},
    ball z1 (ε z1) with hu
  set v : Set ℂ := U ∩ ⋃ z1 ∈ {z1 | z1 ∉ Γ ∧ ∀ z2 ∈ ball z1 (ε z1), z2 ∉ Γ → ¬ Q z2},
    ball z1 (ε z1) with hv
  have huo : IsOpen u := (compl_open Γ).inter (isOpen_biUnion fun _ _ => isOpen_ball)
  have hvo : IsOpen v := (compl_open Γ).inter (isOpen_biUnion fun _ _ => isOpen_ball)
  have huQ : ∀ z ∈ u, Q z := by
    rintro z ⟨hzU, hz⟩
    simp only [mem_iUnion] at hz
    obtain ⟨z1, ⟨hz1, z2, hz2, hz2Γ, hQ2⟩, hzb⟩ := hz
    exact hQ z1 hz1 z2 hz2 hz2Γ hQ2 z hzb hzU
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro z hzu ⟨hzU, hz⟩
    simp only [mem_iUnion] at hz
    obtain ⟨z1, ⟨hz1, hno⟩, hzb⟩ := hz
    exact hno z hzb hzU (huQ z hzu)
  have hcov : U ⊆ u ∪ v := by
    intro z hz
    have hz' : z ∉ Γ := hz
    by_cases h : ∃ z2 ∈ ball z (ε z), z2 ∉ Γ ∧ Q z2
    · left
      exact ⟨hz, mem_biUnion (x := z) ⟨hz', h⟩ (mem_ball_self (hε z hz'))⟩
    · right
      push Not at h
      exact ⟨hz, mem_biUnion (x := z) ⟨hz', fun z2 h2 h2' => h z2 h2 h2'⟩
        (mem_ball_self (hε z hz'))⟩
  have hsub := (compl_conn Γ).subset_left_of_subset_union huo hvo huv hcov
    ⟨z0, hz0, hz0, mem_biUnion (x := z0) ⟨hz0, z0, mem_ball_self (hε z0 hz0), hz0, hQ0⟩
      (mem_ball_self (hε z0 hz0))⟩
  exact fun z hz => huQ z (hsub hz)

/-- Local phase on a ball around `z1`. -/
noncomputable def lph (Γ : Finset ℂ) (k : ℂ → ℝ) (z1 z : ℂ) : ℝ :=
  ∑ γ ∈ Γ, k γ * (Complex.log ((z - γ) / (z1 - γ))).im

lemma ratio_slit (γ z1 z : ℂ) (h : ‖z - z1‖ < ‖z1 - γ‖) :
    (z - γ) / (z1 - γ) ∈ Complex.slitPlane := by
  have hd0 : z1 - γ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) h)
  have heq : (z - γ) / (z1 - γ) = 1 + (z - z1) / (z1 - γ) := by field_simp; ring
  rw [heq, Complex.mem_slitPlane_iff]
  left
  have h1 : ‖(z - z1) / (z1 - γ)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hd0)]; exact h
  have h2 := Complex.abs_re_le_norm ((z - z1) / (z1 - γ))
  rw [Complex.add_re, Complex.one_re]
  have := neg_abs_le ((z - z1) / (z1 - γ)).re
  linarith

lemma log_ratio_hasDerivAt (γ z1 z : ℂ) (h : ‖z - z1‖ < ‖z1 - γ‖) :
    HasDerivAt (fun z => Complex.log ((z - γ) / (z1 - γ))) (1 / (z - γ)) z := by
  have hd0 : z1 - γ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) h)
  have hzγ : z - γ ≠ 0 := by
    intro h0
    have := ratio_slit γ z1 z h
    rw [h0, zero_div] at this
    exact Complex.slitPlane_ne_zero this rfl
  have h1 : HasDerivAt (fun z => (z - γ) / (z1 - γ)) (1 / (z1 - γ)) z := by
    simpa using ((hasDerivAt_id z).sub_const γ).div_const (z1 - γ)
  have h2 := (Complex.hasDerivAt_log (ratio_slit γ z1 z h)).comp z h1
  refine h2.congr_deriv ?_
  field_simp

lemma lph_fderiv (Γ : Finset ℂ) (k : ℂ → ℝ) (z1 z : ℂ) (hz : ∀ γ ∈ Γ, ‖z - z1‖ < ‖z1 - γ‖) :
    DifferentiableAt ℝ (lph Γ k z1) z ∧
      ∀ v : ℂ, fderiv ℝ (lph Γ k z1) z v = (Gk Γ k z * v).im := by
  classical
  have hT : ∀ γ ∈ Γ, HasFDerivAt (fun z => k γ * (Complex.log ((z - γ) / (z1 - γ))).im)
      (k γ • (Complex.imCLM.comp
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (1 / (z - γ))).restrictScalars ℝ :
          ℂ →L[ℝ] ℂ)))) z := by
    intro γ hγ
    have h1 := (log_ratio_hasDerivAt γ z1 z (hz γ hγ)).hasFDerivAt.restrictScalars ℝ
    have h2 := Complex.imCLM.hasFDerivAt.comp z h1
    exact h2.const_mul (k γ)
  have hS' : HasFDerivAt (lph Γ k z1) (∑ γ ∈ Γ, k γ • (Complex.imCLM.comp
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (1 / (z - γ))).restrictScalars ℝ :
          ℂ →L[ℝ] ℂ)))) z :=
    HasFDerivAt.fun_sum hT
  refine ⟨hS'.differentiableAt, fun v => ?_⟩
  rw [hS'.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, Complex.imCLM_apply,
    smul_eq_mul, Gk, Finset.sum_mul, Complex.im_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [show (k γ : ℂ) / (z - γ) * v = (k γ : ℂ) * (v • (1 / (z - γ))) by
    rw [smul_eq_mul]; ring]
  simp

lemma lph_self (Γ : Finset ℂ) (k : ℂ → ℝ) (z1 : ℂ) (hz1 : z1 ∉ Γ) : lph Γ k z1 z1 = 0 := by
  refine Finset.sum_eq_zero fun γ hγ => ?_
  have : z1 - γ ≠ 0 := sub_ne_zero.mpr fun h => hz1 (h ▸ hγ)
  simp [div_self this]

lemma Gk_contAt (Γ : Finset ℂ) (k : ℂ → ℝ) (z : ℂ) (hz : z ∉ Γ) : ContinuousAt (Gk Γ k) z := by
  unfold Gk
  exact tendsto_finset_sum _ fun γ hγ =>
    continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr fun h => hz (h ▸ hγ))

section rep

variable (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Γ : Finset ℂ) (k : ℂ → ℝ) (w : ℂ → V n)
    (hwd : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ w z)
    (hdw : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ w z v = (Gk Γ k z * v).im • reeb H (w z))
    (hwS : ∀ z : ℂ, z ∉ Γ → w z ∈ energySurface H)

include hH hwd hdw hwS in
theorem ball_rep (x : ℝ → V n) (hx : ∀ τ, HasDerivAt x (reeb H (x τ)) τ)
    (z1 : ℂ) (ε : ℝ) (hε : ∀ γ ∈ Γ, ε ≤ ‖z1 - γ‖) (z2 : ℂ) (hz2 : z2 ∈ ball z1 ε) (s : ℝ)
    (h2 : w z2 = x s) :
    ∀ z ∈ ball z1 ε, w z = x (s + lph Γ k z1 z - lph Γ k z1 z2) := by
  have hB := ball_notMem Γ z1 ε hε
  have hlt : ∀ z ∈ ball z1 ε, ∀ γ ∈ Γ, ‖z - z1‖ < ‖z1 - γ‖ := fun z hz γ hγ => by
    rw [mem_ball, dist_eq_norm] at hz; linarith [hε γ hγ]
  exact local_eq H hH x hx (ball z1 ε) isOpen_ball (convex_ball z1 ε) w (Gk Γ k)
    (fun z hz => (Gk_contAt Γ k z (hB z hz)).continuousWithinAt)
    (fun z hz => hwd z (hB z hz)) (fun z hz => hdw z (hB z hz)) (fun z hz => hwS z (hB z hz))
    (lph Γ k z1) (fun z hz => (lph_fderiv Γ k z1 z (hlt z hz)).1)
    (fun z hz => (lph_fderiv Γ k z1 z (hlt z hz)).2) z2 hz2 s h2

include hH hwd hdw hwS in
theorem range_cover (x : ℝ → V n) (hx : ∀ τ, HasDerivAt x (reeb H (x τ)) τ)
    (z0 : ℂ) (hz0 : z0 ∉ Γ) (s0 : ℝ) (h0 : w z0 = x s0) : ∀ z : ℂ, z ∉ Γ → ∃ s, w z = x s := by
  refine propagate Γ (fun z => ∃ s, w z = x s) (fun z1 hz1 => ?_) z0 hz0 ⟨s0, h0⟩
  obtain ⟨ε, hε, hεΓ⟩ := exists_eps Γ z1 hz1
  refine ⟨ε, hε, fun z2 hz2 _ ⟨s, hs⟩ z hz _ => ⟨_, ball_rep H hH Γ k w hwd hdw hwS x hx z1 ε hεΓ z2 hz2
    s hs z hz⟩⟩

end rep

lemma period_of_eq (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (a b : ℝ)
    (h : P.x a = P.x b) : ∀ τ, P.x (τ + (b - a)) = P.x τ := by
  intro τ
  have := ode_uniq H hH univ isOpen_univ isPreconnected_univ (fun _ => 1) continuousOn_const
    (fun τ => P.x (τ + (b - a))) P.x
    (fun t _ => by rw [one_smul]; exact (P.hasDerivAt (t + (b - a))).comp_add_const t (b - a))
    (fun t _ => by rw [one_smul]; exact P.hasDerivAt t)
    (fun t _ => P.mem _) a (mem_univ _) (by simp [h]) τ (mem_univ _)
  exact this

section loopper

variable (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Γ : Finset ℂ) (k : ℂ → ℝ) (w : ℂ → V n)
    (hwd : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ w z)
    (hdw : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ w z v = (Gk Γ k z * v).im • reeb H (w z))
    (hwS : ∀ z : ℂ, z ∉ Γ → w z ∈ energySurface H)

include hH hwd hdw hwS in
theorem loop_period (P : ReebOrbit H) (hcov : ∀ z : ℂ, z ∉ Γ → ∃ s, w z = P.x s) (γ : ℂ)
    (hγ : γ ∈ Γ) : ∀ τ, P.x (τ + 2 * Real.pi * k γ) = P.x τ := by
  classical
  obtain ⟨r, hr, hiso⟩ := exists_iso Γ γ
  set ρ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ ≤ r / 2 := le_rfl
  set Θ := phase Γ k γ ρ with hΘdef
  set D : ℝ → ℝ := fun θ => (Gk Γ k (cl γ ρ θ) * (Complex.I * (cl γ ρ θ - γ))).im with hD
  have hΘ : ∀ θ, HasDerivAt Θ (D θ) θ := phase_hasDerivAt Γ k γ hγ r hr hiso ρ hρ0 hρr
  have hclc : Continuous (cl γ ρ) :=
    continuous_iff_continuousAt.mpr fun θ => (cl_hasDerivAt γ ρ θ).continuousAt
  have hDc : Continuous D := by
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    refine Complex.continuous_im.continuousAt.comp ?_
    refine ContinuousAt.mul ?_ (continuousAt_const.mul (hclc.continuousAt.sub continuousAt_const))
    exact (Gk_contAt Γ k _ (cl_notMem Γ γ r hr hiso ρ hρ0 hρr θ)).comp hclc.continuousAt
  have hy : ∀ θ, HasDerivAt (fun θ => w (cl γ ρ θ)) (D θ • reeb H (w (cl γ ρ θ))) θ := by
    intro θ
    have hm := cl_notMem Γ γ r hr hiso ρ hρ0 hρr θ
    have := (hwd _ hm).hasFDerivAt.comp_hasDerivAt θ (cl_hasDerivAt γ ρ θ)
    rwa [hdw _ hm] at this
  obtain ⟨s, hs⟩ := hcov _ (cl_notMem Γ γ r hr hiso ρ hρ0 hρr 0)
  have hy2 : ∀ θ, HasDerivAt (fun θ => P.x (s + Θ θ - Θ 0))
      (D θ • reeb H (P.x (s + Θ θ - Θ 0))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => s + Θ θ - Θ 0) (D θ) θ := ((hΘ θ).const_add s).sub_const _
    exact (P.hasDerivAt _).scomp θ h1
  have heq := ode_uniq H hH univ isOpen_univ isPreconnected_univ D hDc.continuousOn
    (fun θ => w (cl γ ρ θ)) (fun θ => P.x (s + Θ θ - Θ 0)) (fun t _ => hy t) (fun t _ => hy2 t)
    (fun t _ => hwS _ (cl_notMem Γ γ r hr hiso ρ hρ0 hρr t)) 0 (mem_univ _) (by simp [hs])
    (0 + 2 * Real.pi) (mem_univ _)
  try simp only at heq
  rw [cl_periodic, hs, hΘdef, phase_periodic] at heq
  have h2 : P.x s = P.x (s + 2 * Real.pi * k γ) := by
    rw [heq]; congr 1; ring
  intro τ
  have := period_of_eq H hH P s (s + 2 * Real.pi * k γ) h2 τ
  rwa [add_sub_cancel_left] at this

end loopper

/-- The periods of a periodic Reeb orbit form `T₀ ℤ`. -/
theorem period_gen (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) :
    ∃ T0 > 0, ∀ T : ℝ, (∀ τ, P.x (τ + T) = P.x τ) ↔ ∃ m : ℤ, T = m * T0 := by
  let S : AddSubgroup ℝ :=
    { carrier := {T | ∀ τ, P.x (τ + T) = P.x τ}
      zero_mem' := fun τ => by simp
      add_mem' := fun {a b} ha hb τ => by
        show P.x (τ + (a + b)) = P.x τ
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha τ => by
        show P.x (τ + -a) = P.x τ
        have := ha (τ + -a)
        rw [neg_add_cancel_right] at this
        exact this.symm }
  have hmem : ∀ T, T ∈ S ↔ ∀ τ, P.x (τ + T) = P.x τ := fun T => Iff.rfl
  have hxc : Continuous P.x := continuous_iff_continuousAt.mpr fun τ => (P.hasDerivAt τ).continuousAt
  rcases AddSubgroup.dense_or_cyclic S with hd | ⟨a, ha⟩
  · exfalso
    have hcl : IsClosed (S : Set ℝ) := by
      have : (S : Set ℝ) = ⋂ τ : ℝ, {T | P.x (τ + T) = P.x τ} := by
        ext T; simp [hmem]
      rw [this]
      exact isClosed_iInter fun τ => isClosed_eq (hxc.comp (continuous_const.add continuous_id))
        continuous_const
    have huniv : (S : Set ℝ) = univ := by rw [← hcl.closure_eq]; exact hd.closure_eq
    have hconst : ∀ τ, P.x τ = P.x 0 := fun τ => by
      have : τ ∈ (S : Set ℝ) := huniv ▸ mem_univ τ
      have := (hmem τ).mp this 0
      rwa [zero_add] at this
    have hd0 : HasDerivAt P.x 0 0 := by
      have : P.x = fun _ => P.x 0 := funext hconst
      rw [this]; exact hasDerivAt_const _ _
    have h1 := (P.hasDerivAt 0).unique hd0
    have h2 := (reeb_spec H hH (P.x 0) (P.mem 0)).2.1
    rw [h1] at h2
    rw [← liouvilleCLM_apply, map_zero] at h2
    norm_num at h2
  · rw [← AddSubgroup.zmultiples_eq_closure] at ha
    have hT : P.T ∈ S := fun τ => P.periodic τ
    rw [ha, AddSubgroup.mem_zmultiples_iff] at hT
    obtain ⟨m0, hm0⟩ := hT
    have ha0 : a ≠ 0 := by
      rintro rfl; simp at hm0; linarith [P.T_pos]
    refine ⟨|a|, abs_pos.mpr ha0, fun T => ?_⟩
    rw [← hmem, ha, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨m, rfl⟩
      rcases abs_choice a with h | h
      · exact ⟨m, by rw [h, zsmul_eq_mul]⟩
      · exact ⟨-m, by rw [h, zsmul_eq_mul]; push_cast; ring⟩
    · rintro ⟨m, rfl⟩
      rcases abs_choice a with h | h
      · exact ⟨m, by rw [h, zsmul_eq_mul]⟩
      · exact ⟨-m, by rw [h, zsmul_eq_mul]; push_cast; ring⟩

end DR

end S_DR_g

-- ===== DR_h =====
section S_DR_h


open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace DR

open DP

variable {n : ℕ}

lemma arg_mul_exp (c : ℂ) (hc : c ≠ 0) (L : ℂ) :
    ∃ j : ℤ, Complex.arg (c * Complex.exp L) = Complex.arg c + L.im + j * (2 * Real.pi) := by
  have e1 : c * Complex.exp L = ((‖c‖ * Real.exp L.re : ℝ) : ℂ) *
      Complex.exp (((Complex.arg c + L.im : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c, ← Complex.re_add_im L]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_add]
    ring
  have hpos : 0 < ‖c‖ * Real.exp L.re := mul_pos (norm_pos_iff.mpr hc) (Real.exp_pos _)
  rw [e1, Complex.arg_real_mul _ hpos, Complex.arg_exp_mul_I]
  refine ⟨-toIocDiv (mul_pos two_pos Real.pi_pos) (-Real.pi) (Complex.arg c + L.im), ?_⟩
  have := toIocMod_add_toIocDiv_zsmul (mul_pos two_pos Real.pi_pos) (-Real.pi)
    (Complex.arg c + L.im)
  rw [zsmul_eq_mul] at this
  push_cast
  linarith

section fin

variable (Γ : Finset ℂ) (m : ℂ → ℕ) (C0 : ℝ)

noncomputable def qf (z : ℂ) : ℂ := (C0 : ℂ) * ∏ γ ∈ Γ, (z - γ) ^ m γ

lemma qf_ne (hC0 : C0 ≠ 0) (z : ℂ) (hz : z ∉ Γ) : qf Γ m C0 z ≠ 0 := by
  unfold qf
  refine mul_ne_zero (by exact_mod_cast hC0) ?_
  rw [Finset.prod_ne_zero_iff]
  intro γ hγ
  exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hz (h ▸ hγ))

lemma qf_eq_zero (hm : ∀ γ ∈ Γ, 0 < m γ) (z : ℂ) (hz : z ∈ Γ) : qf Γ m C0 z = 0 := by
  unfold qf
  rw [Finset.prod_eq_zero hz (by rw [sub_self, zero_pow (hm z hz).ne']), mul_zero]

lemma qf_ball (z1 z : ℂ) (hz : ∀ γ ∈ Γ, ‖z - z1‖ < ‖z1 - γ‖) :
    qf Γ m C0 z = qf Γ m C0 z1 *
      Complex.exp (∑ γ ∈ Γ, (m γ : ℂ) * Complex.log ((z - γ) / (z1 - γ))) := by
  have hd0 : ∀ γ ∈ Γ, z1 - γ ≠ 0 := fun γ hγ =>
    norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) (hz γ hγ))
  have hr0 : ∀ γ ∈ Γ, (z - γ) / (z1 - γ) ≠ 0 := fun γ hγ =>
    Complex.slitPlane_ne_zero (ratio_slit γ z1 z (hz γ hγ))
  unfold qf
  rw [Complex.exp_sum, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun γ hγ => ?_
  rw [Complex.exp_nat_mul, Complex.exp_log (hr0 γ hγ), ← mul_pow, mul_div_cancel₀ _ (hd0 γ hγ)]

end fin

/-- Final assembly, from the normal form of `w` and `a`. -/
theorem final (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Γ : Finset ℂ) (hΓ : Γ.Nonempty)
    (k : ℂ → ℝ) (hk : ∀ γ ∈ Γ, 0 < k γ) (w : ℂ → V n)
    (hwd : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ w z)
    (hdw : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ w z v = (Gk Γ k z * v).im • reeb H (w z))
    (hwS : ∀ z : ℂ, z ∉ Γ → w z ∈ energySurface H) (c0 : ℝ) (u : ℂ → V n)
    (huz : ∀ z : ℂ, z ∉ Γ →
      u z = Real.exp (2 * (∑ γ ∈ Γ, k γ * Real.log ‖z - γ‖ + c0)) • w z) :
    ∃ p : Polynomial ℂ, 0 < p.natDegree ∧ {z | p.eval z = 0} = ↑Γ ∧
      ∃ P : ReebOrbit H, ∀ z ∉ Γ, u z = trivialCylinder P (p.eval z) := by
  classical
  obtain ⟨γ1, hγ1⟩ := hΓ
  obtain ⟨P1, -, z0, hz0, s0, h0⟩ := exists_orbit H hH Γ k γ1 hγ1 (hk γ1 hγ1) w hwd hdw hwS
  have hcov := range_cover H hH Γ k w hwd hdw hwS P1.x P1.hasDerivAt z0 hz0 s0 h0
  have hper := fun γ hγ => loop_period H hH Γ k w hwd hdw hwS P1 hcov γ hγ
  obtain ⟨T0, hT0, hgen⟩ := period_gen H hH P1
  have hmex : ∀ γ, ∃ m : ℕ, γ ∈ Γ → 2 * Real.pi * k γ = m * T0 ∧ 0 < m := by
    intro γ
    by_cases hγ : γ ∈ Γ
    · obtain ⟨j, hj⟩ := (hgen _).mp (hper γ hγ)
      have hpos : 0 < (j : ℝ) * T0 := by rw [← hj]; have := hk γ hγ; positivity
      have hj0 : 0 < j := by
        have : (0 : ℝ) < j := pos_of_mul_pos_left hpos hT0.le
        exact_mod_cast this
      refine ⟨j.toNat, fun _ => ⟨?_, by omega⟩⟩
      rw [hj]
      congr 1
      have : ((j.toNat : ℤ) : ℝ) = (j : ℝ) := by rw [Int.toNat_of_nonneg hj0.le]
      exact_mod_cast this.symm
    · exact ⟨0, fun h => absurd h hγ⟩
  choose m hm using hmex
  have hmk : ∀ γ ∈ Γ, (m γ : ℝ) = 2 * Real.pi * k γ / T0 := fun γ hγ => by
    rw [(hm γ hγ).1]; field_simp
  have hint : ∀ τ (j : ℤ), P1.x (τ + j * T0) = P1.x τ := fun τ j => (hgen _).mpr ⟨j, rfl⟩ τ
  set C0 : ℝ := Real.exp (2 * c0 * Real.pi / T0) with hC0
  have hC0pos : 0 < C0 := Real.exp_pos _
  set p : Polynomial ℂ := Polynomial.C (C0 : ℂ) * ∏ γ ∈ Γ, (Polynomial.X - Polynomial.C γ) ^ m γ
    with hp
  have hpq : ∀ z, p.eval z = qf Γ m C0 z := fun z => by
    simp [hp, qf, Polynomial.eval_prod]
  have hzero : {z | p.eval z = 0} = (↑Γ : Set ℂ) := by
    ext z
    simp only [mem_setOf_eq, hpq, Finset.mem_coe]
    constructor
    · intro h
      by_contra hz
      exact qf_ne Γ m C0 hC0pos.ne' z hz h
    · intro hz
      exact qf_eq_zero Γ m C0 (fun γ hγ => (hm γ hγ).2) z hz
  have hdeg : 0 < p.natDegree := by
    by_contra h0'
    push Not at h0'
    have hc := Polynomial.eq_C_of_natDegree_le_zero h0'
    have e1 : p.eval γ1 = p.eval z0 := by rw [hc]; simp
    rw [hpq, hpq, qf_eq_zero Γ m C0 (fun γ hγ => (hm γ hγ).2) γ1 hγ1] at e1
    exact qf_ne Γ m C0 hC0pos.ne' z0 hz0 e1.symm
  set τ1 := s0 - T0 * Complex.arg (qf Γ m C0 z0) / (2 * Real.pi) with hτ1
  let P : ReebOrbit H :=
    { x := fun τ => P1.x (τ + τ1)
      T := T0
      T_pos := hT0
      mem := fun τ => P1.mem _
      hasDerivAt := fun τ => (P1.hasDerivAt (τ + τ1)).comp_add_const τ τ1
      periodic := fun τ => by
        show P1.x (τ + T0 + τ1) = P1.x (τ + τ1)
        have := hint (τ + τ1) 1
        rw [Int.cast_one, one_mul] at this
        rw [← this]; congr 1; ring }
  -- arg relation on balls
  have hargq : ∀ z1 z : ℂ, z1 ∉ Γ → (∀ γ ∈ Γ, ‖z - z1‖ < ‖z1 - γ‖) → ∃ j : ℤ,
      T0 * Complex.arg (qf Γ m C0 z) / (2 * Real.pi) =
        T0 * Complex.arg (qf Γ m C0 z1) / (2 * Real.pi) + lph Γ k z1 z + j * T0 := by
    intro z1 z hz1 hz
    obtain ⟨j, hj⟩ := arg_mul_exp (qf Γ m C0 z1) (qf_ne Γ m C0 hC0pos.ne' z1 hz1)
      (∑ γ ∈ Γ, (m γ : ℂ) * Complex.log ((z - γ) / (z1 - γ)))
    rw [← qf_ball Γ m C0 z1 z hz] at hj
    refine ⟨j, ?_⟩
    rw [hj]
    have hL : (∑ γ ∈ Γ, (m γ : ℂ) * Complex.log ((z - γ) / (z1 - γ))).im =
        2 * Real.pi / T0 * lph Γ k z1 z := by
      rw [Complex.im_sum, lph, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      rw [hmk γ hγ]
      field_simp
    rw [hL]
    field_simp
  have hang : ∀ z : ℂ, z ∉ Γ →
      w z = P1.x (T0 * Complex.arg (qf Γ m C0 z) / (2 * Real.pi) + τ1) := by
    refine propagate Γ (fun z => w z = P1.x (T0 * Complex.arg (qf Γ m C0 z) / (2 * Real.pi) + τ1))
      (fun z1 hz1 => ?_) z0 hz0 (by rw [h0, hτ1]; congr 1; ring)
    obtain ⟨ε, hε, hεΓ⟩ := exists_eps Γ z1 hz1
    refine ⟨ε, hε, fun z2 hz2 _ hQ2 z hz _ => ?_⟩
    have hlt : ∀ y ∈ ball z1 ε, ∀ γ ∈ Γ, ‖y - z1‖ < ‖z1 - γ‖ := fun y hy γ hγ => by
      rw [mem_ball, dist_eq_norm] at hy; linarith [hεΓ γ hγ]
    have hr := ball_rep H hH Γ k w hwd hdw hwS P1.x P1.hasDerivAt z1 ε hεΓ z2 hz2 _ hQ2 z hz
    obtain ⟨j, hj⟩ := hargq z1 z hz1 (hlt z hz)
    obtain ⟨j2, hj2⟩ := hargq z1 z2 hz1 (hlt z2 hz2)
    show w z = _
    rw [hr, hj, hj2]
    set X := T0 * Complex.arg (qf Γ m C0 z1) / (2 * Real.pi) + lph Γ k z1 z + τ1 with hX
    have key : ∀ a b : ℝ, ∀ i i' : ℤ, a = X + i * T0 → b = X + i' * T0 → P1.x a = P1.x b := by
      intro a b i i' ha hb
      rw [ha, hb, hint, hint]
    exact key _ _ j2 j (by ring) (by ring)
  have hrad : ∀ z : ℂ, z ∉ Γ → ‖qf Γ m C0 z‖ ^ (T0 / Real.pi) =
      Real.exp (2 * (∑ γ ∈ Γ, k γ * Real.log ‖z - γ‖ + c0)) := by
    intro z hz
    have hne : ∀ γ ∈ Γ, ‖z - γ‖ ≠ 0 := fun γ hγ =>
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => hz (h ▸ hγ))
    have hN : ‖qf Γ m C0 z‖ = C0 * ∏ γ ∈ Γ, ‖z - γ‖ ^ m γ := by
      simp only [qf, norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hC0pos]
    have hpos : 0 < C0 * ∏ γ ∈ Γ, ‖z - γ‖ ^ m γ :=
      mul_pos hC0pos (Finset.prod_pos fun γ hγ => pow_pos
        (lt_of_le_of_ne (norm_nonneg _) (hne γ hγ).symm) _)
    rw [hN, Real.rpow_def_of_pos hpos, Real.log_mul hC0pos.ne'
      (Finset.prod_ne_zero_iff.mpr fun γ hγ => pow_ne_zero _ (hne γ hγ)),
      Real.log_prod (fun γ hγ => pow_ne_zero _ (hne γ hγ)), hC0, Real.log_exp]
    congr 1
    simp only [Real.log_pow]
    have hp := Real.pi_pos
    have hs : ∑ γ ∈ Γ, (m γ : ℝ) * Real.log ‖z - γ‖ * (T0 / Real.pi) =
        2 * ∑ γ ∈ Γ, k γ * Real.log ‖z - γ‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [hmk γ hγ]
      field_simp
    rw [add_mul, Finset.sum_mul, hs]
    field_simp
    ring
  refine ⟨p, hdeg, hzero, P, fun z hz => ?_⟩
  show u z = ‖p.eval z‖ ^ (T0 / Real.pi) • P1.x (T0 * Complex.arg (p.eval z) / (2 * Real.pi) + τ1)
  rw [hpq, hrad z hz, ← hang z hz, huz z hz]

end DR

end S_DR_h

-- ===== DR_i =====
section S_DR_i


open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace DR

variable {n : ℕ}

theorem main (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u)
    (hnc : ∃ z₁ ∉ Γ, ∃ z₂ ∉ Γ, u z₁ ≠ u z₂)
    (hneg : ∀ z₀ ∈ Γ, Tendsto (fun z => aCoord H (u z)) (𝓝[≠] z₀) atBot)
    (hzero : dlambdaEnergy H (↑Γ)ᶜ u = 0) :
    ∃ p : Polynomial ℂ, 0 < p.natDegree ∧ {z | p.eval z = 0} = ↑Γ ∧
      ∃ P : ReebOrbit H, ∀ z ∉ Γ, u z = trivialCylinder P (p.eval z) := by
  classical
  have hUo := compl_open Γ
  obtain ⟨hgd, ⟨M, hM⟩, hda, hdw⟩ := core H hH J hJ (↑Γ)ᶜ hUo u hu hzero
  obtain ⟨κ, hκ⟩ := partial_fractions Γ _ hgd M (fun z hz s hs hb => hM z hz s hs hb)
  obtain ⟨hsm, hu0, -, -⟩ := hu
  obtain ⟨hasm, hwsm⟩ := DQ.smooth_aw H hH J hJ (↑Γ)ᶜ u hsm hu0
  obtain ⟨-, -, -, hrel, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set a := fun z => aCoord H (u z) with hadef
  set w := fun z => proj H (u z) with hwdef
  have had : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ a z := fun z hz =>
    (hasm.contDiffAt (hUo.mem_nhds hz)).differentiableAt (by simp)
  have hwd : ∀ z : ℂ, z ∉ Γ → DifferentiableAt ℝ w z := fun z hz =>
    (hwsm.contDiffAt (hUo.mem_nhds hz)).differentiableAt (by simp)
  have hda' : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ a z v = ((∑ γ ∈ Γ, κ γ / (z - γ)) * v).re :=
    fun z hz v => by rw [hda z hz v, hκ z hz]
  have hreal := kappa_real Γ a had κ hda'
  set k : ℂ → ℝ := fun γ => (κ γ).re with hkdef
  have hκk : ∀ γ ∈ Γ, κ γ = (k γ : ℂ) := fun γ hγ =>
    Complex.ext (by simp [hkdef]) (by simp [hreal γ hγ])
  have hsumk : ∀ z, ∑ γ ∈ Γ, κ γ / (z - γ) = Gk Γ k z := fun z =>
    Finset.sum_congr rfl fun γ hγ => by rw [hκk γ hγ]
  have hda'' : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ,
      fderiv ℝ a z v = ((∑ γ ∈ Γ, (k γ : ℂ) / (z - γ)) * v).re :=
    fun z hz v => by rw [hda' z hz v, hsumk]; rfl
  obtain ⟨c0, haeq⟩ := a_eq Γ a had k hda''
  have hk : ∀ γ ∈ Γ, 0 < k γ := fun γ hγ => kappa_pos Γ a k c0 haeq γ hγ (hneg γ hγ)
  have hdw' : ∀ z : ℂ, z ∉ Γ → ∀ v : ℂ, fderiv ℝ w z v = (Gk Γ k z * v).im • reeb H (w z) :=
    fun z hz v => by rw [hdw z hz v, hκ z hz, hsumk]
  have hwS : ∀ z : ℂ, z ∉ Γ → w z ∈ energySurface H := fun z hz => (hrel _ (hu0 z hz)).1
  have huz : ∀ z : ℂ, z ∉ Γ →
      u z = Real.exp (2 * (∑ γ ∈ Γ, k γ * Real.log ‖z - γ‖ + c0)) • w z := fun z hz => by
    rw [← haeq z hz]; exact (hrel _ (hu0 z hz)).2
  have hΓ : Γ.Nonempty := by
    by_contra hΓ
    rw [Finset.not_nonempty_iff_eq_empty] at hΓ
    obtain ⟨z₁, h1, z₂, h2, h12⟩ := hnc
    have hwc : ∀ z ∈ ((↑Γ)ᶜ : Set ℂ), w z = w z₂ := fun z hz =>
      hUo.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (compl_conn Γ)
        (fun y hy => (hwd y hy).differentiableWithinAt)
        (fun y hy => by ext1 v; simp [hdw' y hy v, Gk, hΓ]) hz h2
    apply h12
    rw [huz z₁ h1, huz z₂ h2, hwc z₁ h1]
    simp [hΓ]
  exact final H hH Γ hΓ k hk w hwd hdw' hwS c0 u huz

end DR

theorem solution {n : ℕ} (H : FiniteEnergyPlane.V n → ℝ)
    (hH : FiniteEnergyPlane.IsStrictlyStarShapedLevel H)
    (J : FiniteEnergyPlane.V n → FiniteEnergyPlane.V n →L[ℝ] FiniteEnergyPlane.V n)
    (hJ : FiniteEnergyPlane.IsCompatibleXiStructure H J) (Γ : Finset ℂ)
    (u : ℂ → FiniteEnergyPlane.V n)
    (hu : FiniteEnergyPlane.IsFiniteEnergyCurve H J (↑Γ)ᶜ u)
    (hnc : ∃ z₁ ∉ Γ, ∃ z₂ ∉ Γ, u z₁ ≠ u z₂)
    (hneg : ∀ z₀ ∈ Γ, Tendsto (fun z => FiniteEnergyPlane.aCoord H (u z)) (𝓝[≠] z₀) atBot)
    (hzero : FiniteEnergyPlane.dlambdaEnergy H (↑Γ)ᶜ u = 0) :
    ∃ p : Polynomial ℂ, 0 < p.natDegree ∧ {z | p.eval z = 0} = ↑Γ ∧
      ∃ P : FiniteEnergyPlane.ReebOrbit H, ∀ z ∉ Γ,
        u z = FiniteEnergyPlane.trivialCylinder P (p.eval z) :=
  DR.main H hH J hJ Γ u hu hnc hneg hzero

end S_DR_i
