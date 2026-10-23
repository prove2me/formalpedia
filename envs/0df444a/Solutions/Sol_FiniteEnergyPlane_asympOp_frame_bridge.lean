-- Prove2me | solution 1 for FiniteEnergyPlane.asympOp_frame_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:00:50.020182+00:00
-- url     : https://prove2.me/submissions/a386ebd1-d57f-415e-bdf0-c3bddff1aff5

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_spec
import Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame


set_option linter.all false

open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace IsoSpec
open FiniteEnergyPlane
open scoped ContDiff

variable {n : ℕ}

lemma contDiff_j0 : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 fun k => ?_
  unfold j0
  by_cases h : (k : ℕ) % 2 = 0
  · simp only [h, dite_true]
    exact (contDiff_apply ℝ ℝ _).neg
  · simp only [h, dite_false]
    exact contDiff_apply ℝ ℝ _

lemma contDiff_hamVF (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamVF H) := by
  have hg : ContDiff ℝ ∞ (grad H) := by
    refine contDiff_pi.2 fun k => ?_
    exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact contDiff_j0.comp hg

lemma contDiff_liouville : ContDiff ℝ ∞ (fun p : V n × V n => liouville p.1 p.2) := by
  unfold liouville omega0 dot
  refine ContDiff.div_const (ContDiff.sum fun k _ => ?_) _
  exact ((contDiff_apply ℝ ℝ k).comp (contDiff_j0.comp contDiff_fst)).mul
    ((contDiff_apply ℝ ℝ k).comp contDiff_snd)

lemma liouvilleCLM_apply (x v : V n) : liouvilleCLM x v = liouville x v := by
  simp [liouvilleCLM, liouville, omega0, dot, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end IsoSpec

namespace FrameBridge

variable {n : ℕ}

lemma j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; by_cases h : (k : ℕ) % 2 = 0 <;> simp [j0, h]; ring

lemma j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; by_cases h : (k : ℕ) % 2 = 0 <;> simp [j0, h]

lemma om_add_left (u u' v : V n) : omega0 (u + u') v = omega0 u v + omega0 u' v := by
  simp [omega0, dot, j0_add, add_mul, Finset.sum_add_distrib]

lemma om_smul_left (c : ℝ) (u v : V n) : omega0 (c • u) v = c * omega0 u v := by
  simp [omega0, dot, j0_smul, Finset.mul_sum, mul_assoc]

lemma om_add_right (u v v' : V n) : omega0 u (v + v') = omega0 u v + omega0 u v' := by
  simp [omega0, dot, mul_add, Finset.sum_add_distrib]

lemma om_smul_right (c : ℝ) (u v : V n) : omega0 u (c • v) = c * omega0 u v := by
  simp [omega0, dot, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def om : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V n →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ omega0 om_add_left om_smul_left om_add_right om_smul_right)

@[simp] lemma om_apply (u v : V n) : om u v = omega0 u v := rfl

/-- the coordinate involution `k ↦ k xor 1` -/
def sw (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

lemma sw_sw (k : Fin (2 * (n + 1))) : sw (sw k) = k := by
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [sw, h, h', ↓reduceDIte, Fin.ext_iff]; omega
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [sw, h, h', ↓reduceDIte, Fin.ext_iff]; omega

lemma om_antisymm (u v : V n) : omega0 u v = -omega0 v u := by
  have e : Function.Involutive (sw (n := n)) := sw_sw
  simp only [omega0, dot]
  rw [← Equiv.sum_comp e.toPerm (fun k => j0 u k * v k)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Involutive.coe_toPerm, j0, sw]
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [h, h', ↓reduceDIte]
    have : (⟨(k : ℕ) + 1 - 1, by omega⟩ : Fin (2 * (n + 1))) = k := by ext; simp
    rw [this]; ring
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [h, h', ↓reduceDIte]
    have : (⟨(k : ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp; omega
    rw [this]; ring


open CauchyRiemannIndex

/-- `J₀` acting on `ℝ^{2n}`. -/
noncomputable abbrev JL (n : ℕ) : Vec n →L[ℝ] Vec n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (J₀ n))

noncomputable abbrev e (i : Fin n ⊕ Fin n) : Vec n := EuclideanSpace.single i (1 : ℝ)

lemma JL_apply (c : Vec n) : JL n c = Matrix.toEuclideanLin (J₀ n) c := rfl

lemma JJ (c : Vec n) : Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (J₀ n) c) = -c := by
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.J_squared]
  ext i; simp [Matrix.neg_mulVec]

lemma vec_expand (c : Vec n) : c = ∑ j, c j • e j := by
  have := (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℝ).sum_repr c
  simpa [e] using this.symm

lemma om_zero_left (v : V n) : omega0 0 v = 0 := by rw [← om_apply]; simp
lemma om_zero_right (v : V n) : omega0 v 0 = 0 := by rw [← om_apply, map_zero]
lemma om_sub_left (u u' v : V n) : omega0 (u - u') v = omega0 u v - omega0 u' v := by
  simp only [← om_apply, map_sub, ContinuousLinearMap.sub_apply]
lemma om_neg_left (u v : V n) : omega0 (-u) v = -omega0 u v := by
  simp only [← om_apply, map_neg, ContinuousLinearMap.neg_apply]
lemma om_sum_left {ι : Type*} (s : Finset ι) (f : ι → V n) (v : V n) :
    omega0 (∑ i ∈ s, f i) v = ∑ i ∈ s, omega0 (f i) v := by
  simp only [← om_apply, map_sum, ContinuousLinearMap.sum_apply]

/-! ### `ξ` is a linear subspace -/

lemma liou_lin (x : V n) : (fun v => liouville x v) = fun v => om x v / 2 := rfl

lemma xi_add {H : V n → ℝ} {y u v : V n} (hu : IsInXi H y u) (hv : IsInXi H y v) :
    IsInXi H y (u + v) := by
  refine ⟨?_, ?_⟩
  · have h1 := hu.1; have h2 := hv.1
    simp only [liouville, ← om_apply] at h1 h2 ⊢; rw [map_add]; linarith
  · rw [map_add, hu.2, hv.2, add_zero]

lemma xi_smul {H : V n → ℝ} {y u : V n} (c : ℝ) (hu : IsInXi H y u) : IsInXi H y (c • u) := by
  refine ⟨?_, ?_⟩
  · have h1 := hu.1
    simp only [liouville, ← om_apply] at h1 ⊢; rw [map_smul, smul_eq_mul]
    have : om y u = 0 := by linarith
    rw [this]; simp
  · rw [map_smul, hu.2, smul_zero]

lemma xi_neg {H : V n → ℝ} {y u : V n} (hu : IsInXi H y u) : IsInXi H y (-u) := by
  simpa using xi_smul (-1) hu

lemma xi_sub {H : V n → ℝ} {y u v : V n} (hu : IsInXi H y u) (hv : IsInXi H y v) :
    IsInXi H y (u - v) := by
  simpa [sub_eq_add_neg] using xi_add hu (xi_neg hv)

/-! ### Unitary frames -/

section frame
variable {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
  {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z)
include hZ

lemma fr_coord (t : ℝ) (a : Vec n) (i : Fin n ⊕ Fin n) :
    omega0 (Z t a) (Z t (e i)) = Matrix.toEuclideanLin (J₀ n) a i := by
  rw [(hZ.2.2 t).2.2.2 a (e i)]
  simp [e, EuclideanSpace.inner_single_right]

lemma fr_inj (t : ℝ) (a : Vec n) (h : Z t a = 0) : a = 0 := by
  have h1 : ∀ b, inner ℝ (Matrix.toEuclideanLin (J₀ n) a) b = 0 := by
    intro b; rw [← (hZ.2.2 t).2.2.2 a b, h, om_zero_left]
  have h2 : Matrix.toEuclideanLin (J₀ n) a = 0 := inner_self_eq_zero.1 (h1 _)
  have := JJ a
  rw [h2, map_zero] at this
  exact (neg_eq_zero.1 this.symm)

end frame

/-- Coordinates `w ↦ (ω₀(w, Z eᵢ))ᵢ`. -/
noncomputable def coordL (Z : Vec n →L[ℝ] V n) : V n →L[ℝ] Vec n :=
  (EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (om (n := n)).flip (Z (e i)))

lemma coordL_apply (Z : Vec n →L[ℝ] V n) (w : V n) (i : Fin n ⊕ Fin n) :
    coordL Z w i = omega0 w (Z (e i)) := rfl

/-- The inverse of a unitary frame on `ξ`. -/
noncomputable def Zinv (Z : Vec n →L[ℝ] V n) : V n →L[ℝ] Vec n := -((JL n).comp (coordL Z))

section frame2
variable {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
  {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z)
include hZ

lemma coordL_Z (t : ℝ) (b : Vec n) : coordL (Z t) (Z t b) = Matrix.toEuclideanLin (J₀ n) b := by
  ext i; rw [coordL_apply, fr_coord hZ]

lemma Zinv_Z (t : ℝ) (b : Vec n) : Zinv (Z t) (Z t b) = b := by
  simp only [Zinv, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, coordL_Z hZ,
    JL_apply, JJ, neg_neg]

lemma Z_Zinv (t : ℝ) (w : V n) (hw : IsInXi H (P.x (P.T * t)) w) : Z t (Zinv (Z t) w) = w := by
  obtain ⟨b, rfl⟩ := (hZ.2.2 t).2.1 w hw
  rw [Zinv_Z hZ]

end frame2


/-! ### Analytic facts along the orbit -/

def shiftOrbit {H : V n → ℝ} (P : ReebOrbit H) (τ : ℝ) : ReebOrbit H where
  x := fun s => P.x (s + τ)
  T := P.T
  T_pos := P.T_pos
  mem := fun s => P.mem _
  hasDerivAt := fun s => (P.hasDerivAt (s + τ)).comp_add_const s τ
  periodic := fun s => by
    show P.x (s + P.T + τ) = P.x (s + τ)
    rw [show s + P.T + τ = (s + τ) + P.T by ring]; exact P.periodic _

lemma om_cont : Continuous fun p : V n × V n => omega0 p.1 p.2 := by
  have : (fun p : V n × V n => omega0 p.1 p.2) = fun p => om p.1 p.2 := rfl
  rw [this]; exact (om.continuous.comp continuous_fst).clm_apply continuous_snd

lemma xi_limit {H : V n → ℝ} (hH : ContDiff ℝ 1 H) {l : Filter ℝ} [l.NeBot] {f g : ℝ → V n}
    {y v : V n} (hf : Tendsto f l (𝓝 y)) (hg : Tendsto g l (𝓝 v))
    (hev : ∀ᶠ s in l, IsInXi H (f s) (g s)) : IsInXi H y v := by
  constructor
  · have h1 : Tendsto (fun s => liouville (f s) (g s)) l (𝓝 (liouville y v)) := by
      have := (om_cont (n := n)).continuousAt (x := (y, v))
      have h := (this.tendsto.comp (hf.prodMk_nhds hg)).div_const 2
      simpa [liouville] using h
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (hev.mono fun s hs => hs.1.symm))
  · have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
    have h1 : Tendsto (fun s => fderiv ℝ H (f s) (g s)) l (𝓝 (fderiv ℝ H y v)) := by
      have := ((hc.comp continuous_fst).clm_apply (continuous_snd (X := V n) (Y := V n))).continuousAt
        (x := (y, v))
      exact this.tendsto.comp (hf.prodMk_nhds hg)
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (hev.mono fun s hs => hs.2.symm))

/-- derivative of `ω₀(f, g)` -/
lemma hasDerivAt_om {f g : ℝ → V n} {f' g' : V n} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => omega0 (f s) (g s)) (omega0 f' (g t) + omega0 (f t) g') t := by
  have h1 : HasDerivAt (fun s => om (f s)) (om f') t := om.hasFDerivAt.comp_hasDerivAt t hf
  exact h1.clm_apply hg

section orbit
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
include hH

/-- `DR` is infinitesimally symplectic on `ξ` along the orbit. -/
lemma skew (τ : ℝ) (u w : V n) (hu : IsInXi H (P.x τ) u) (hw : IsInXi H (P.x τ) w) :
    omega0 (fderiv ℝ (reeb H) (P.x τ) u) w + omega0 u (fderiv ℝ (reeb H) (P.x τ) w) = 0 := by
  set Q := shiftOrbit P τ
  have hQ0 : Q.x 0 = P.x τ := by simp [Q, shiftOrbit]
  obtain ⟨Φ, hΦ, -⟩ := (linReebFlow_spec H hH Q).1
  have hsp := ((linReebFlow_spec H hH Q).2 Φ hΦ).1
  rw [← hQ0] at hu hw
  have hd : ∀ v : V n, HasDerivAt (fun σ => Φ σ v) (fderiv ℝ (reeb H) (Q.x 0) v) 0 := by
    intro v
    have := (hΦ.2 0).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa [hΦ.1] using this
  have h1 := hasDerivAt_om (hd u) (hd w)
  have h2 : (fun σ => omega0 (Φ σ u) (Φ σ w)) = fun _ => omega0 u w := by
    funext σ; exact (hsp σ u w hu hw).2
  rw [h2] at h1
  have := h1.unique (hasDerivAt_const _ _)
  simpa [hΦ.1, hQ0] using this

/-- `P.x` is smooth. -/
lemma reeb_smooth : ∃ U : Set (V n), IsOpen U ∧ ContDiffOn ℝ ∞ (reeb H) U ∧ ∀ τ, P.x τ ∈ U := by
  set D : V n → ℝ := fun y => liouville y (hamVF H y) with hDdef
  have hD : ContDiff ℝ ∞ D := by
    have h1 := IsoSpec.contDiff_liouville (n := n)
    have h2 := IsoSpec.contDiff_hamVF H hH.1
    exact h1.comp (contDiff_id.prodMk h2)
  refine ⟨{y | 0 < D y}, isOpen_lt continuous_const hD.continuous, ?_, fun τ =>
    (reeb_spec H hH (P.x τ) (P.mem τ)).1⟩
  have : reeb H = fun y => (D y)⁻¹ • hamVF H y := rfl
  rw [this]
  have h1 : ContDiffOn ℝ ∞ (fun y => (D y)⁻¹) {y | 0 < D y} :=
    hD.contDiffOn.inv fun y hy => ne_of_gt hy
  exact h1.smul (IsoSpec.contDiff_hamVF H hH.1).contDiffOn

lemma x_smooth : ContDiff ℝ ∞ P.x := by
  obtain ⟨U, hU, hR, hxU⟩ := reeb_smooth hH P
  have hdx : deriv P.x = fun τ => reeb H (P.x τ) := funext fun τ => (P.hasDerivAt τ).deriv
  have hdiff : Differentiable ℝ P.x := fun τ => (P.hasDerivAt τ).differentiableAt
  have key : ∀ m : ℕ, ContDiff ℝ m P.x := by
    intro m
    induction m with
    | zero => exact contDiff_zero.2 hdiff.continuous
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, ?_⟩
      rw [hdx]
      exact (hR.of_le (by exact_mod_cast le_top)).comp_contDiff ih hxU
  exact contDiff_infty.2 key

lemma A_smooth : ContDiff ℝ ∞ (fun t => fderiv ℝ (reeb H) (P.x (P.T * t))) := by
  obtain ⟨U, hU, hR, hxU⟩ := reeb_smooth hH P
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (reeb H)) U := hR.fderiv_of_isOpen hU (by simp)
  exact h1.comp_contDiff ((x_smooth hH P).comp (contDiff_const.mul contDiff_id)) fun t => hxU _

end orbit


/-- `A(t) = DR(x(Tt))` -/
noncomputable def Aop {H : V n → ℝ} (P : ReebOrbit H) (t : ℝ) : V n →L[ℝ] V n :=
  fderiv ℝ (reeb H) (P.x (P.T * t))

/-- `M(t) = Z'(t) - T A(t) Z(t)` -/
noncomputable def Mop {H : V n → ℝ} (P : ReebOrbit H) (Z : ℝ → Vec n →L[ℝ] V n) (t : ℝ) :
    Vec n →L[ℝ] V n :=
  deriv Z t - P.T • (Aop P t).comp (Z t)

/-- the matrix `S∞(t)ᵢⱼ = ω₀(M eⱼ, Z eᵢ)` -/
noncomputable def Sinf {H : V n → ℝ} (P : ReebOrbit H) (Z : ℝ → Vec n →L[ℝ] V n) (t : ℝ) :
    Mat n := Matrix.of fun i j => omega0 (Mop P Z t (e j)) (Z t (e i))

section frame3
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V n → V n →L[ℝ] V n}
  {P : ReebOrbit H} {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z)
include hZ

lemma Zdiff : Differentiable ℝ Z := hZ.1.differentiable (by simp)

lemma F4 (t : ℝ) (a b : Vec n) :
    omega0 (deriv Z t a) (Z t b) + omega0 (Z t a) (deriv Z t b) = 0 := by
  have hd : ∀ c : Vec n, HasDerivAt (fun s => Z s c) (deriv Z t c) t := fun c => by
    simpa using ((Zdiff hZ) t).hasDerivAt.clm_apply (hasDerivAt_const t c)
  have h1 := hasDerivAt_om (hd a) (hd b)
  have h2 : (fun s => omega0 (Z s a) (Z s b)) = fun _ =>
      inner ℝ (Matrix.toEuclideanLin (J₀ n) a) b := funext fun s => (hZ.2.2 s).2.2.2 a b
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

include hH

lemma F2 (t : ℝ) (a : Vec n) : IsInXi H (P.x (P.T * t)) (Mop P Z t a) := by
  set τ := P.T * t
  set Q := shiftOrbit P τ
  obtain ⟨Φ, hΦ, -⟩ := (linReebFlow_spec H hH Q).1
  have hsp := ((linReebFlow_spec H hH Q).2 Φ hΦ).1
  set v0 := Z t a
  have hv0 : IsInXi H (Q.x 0) v0 := by
    show IsInXi H (P.x (0 + τ)) v0; rw [zero_add]; exact (hZ.2.2 t).1 a
  set c : ℝ → V n := fun s => Z (t + s) a - Φ (P.T * s) v0
  have hmem : ∀ s, IsInXi H (P.x (P.T * (t + s))) (c s) := by
    intro s
    refine xi_sub ((hZ.2.2 (t + s)).1 a) ?_
    have := (hsp (P.T * s) v0 v0 hv0 hv0).1
    have e1 : Q.x (P.T * s) = P.x (P.T * (t + s)) := by
      show P.x (P.T * s + τ) = _; congr 1; simp only [τ]; ring
    rwa [e1] at this
  have hc0 : c 0 = 0 := by simp [c, hΦ.1, v0]
  have hQ0 : Q.x 0 = P.x τ := by show P.x (0 + τ) = _; rw [zero_add]
  have hder : HasDerivAt c (Mop P Z t a) 0 := by
    have hz : HasDerivAt (fun s => Z (t + s) a) (deriv Z t a) 0 := by
      have h := ((Zdiff hZ) (t + 0)).hasDerivAt.comp_const_add t 0
      rw [add_zero] at h
      simpa using h.clm_apply (hasDerivAt_const (0 : ℝ) a)
    have hp : HasDerivAt (fun s => Φ (P.T * s)) (P.T • (fderiv ℝ (reeb H) (Q.x 0)).comp (Φ 0)) 0 := by
      have h1 : HasDerivAt Φ ((fderiv ℝ (reeb H) (Q.x 0)).comp (Φ 0)) (P.T * 0) := by
        rw [mul_zero]; exact hΦ.2 0
      have h2 : HasDerivAt (fun s : ℝ => P.T * s) P.T 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul P.T
      exact h1.scomp 0 h2
    refine (hz.sub (hp.clm_apply (hasDerivAt_const (0 : ℝ) v0))).congr_deriv ?_
    simp [Mop, Aop, hΦ.1, hQ0, v0, τ]
  have hsl := hder.tendsto_slope_zero
  refine xi_limit (hH.1.of_le (by simp)) (f := fun s => P.x (P.T * (t + s)))
    (g := fun s => s⁻¹ • (c (0 + s) - c 0)) ?_ hsl ?_
  · have : Continuous fun s => P.x (P.T * (t + s)) :=
      (x_smooth hH P).continuous.comp (continuous_const.mul (continuous_const.add continuous_id))
    have h := this.tendsto 0
    simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · refine Eventually.of_forall fun s => ?_
    rw [hc0, sub_zero, zero_add]
    exact xi_smul _ (hmem s)

lemma S_apply (t : ℝ) (c : Vec n) (i : Fin n ⊕ Fin n) :
    Matrix.toEuclideanLin (Sinf P Z t) c i = omega0 (Mop P Z t c) (Z t (e i)) := by
  conv_rhs => rw [vec_expand c]
  rw [map_sum, om_sum_left]
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Sinf, Matrix.of_apply,
    map_smul, om_smul_left]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- `S c = J₀ b` where `Z b = M c`. -/
lemma S_eq (t : ℝ) (c : Vec n) :
    Z t (Zinv (Z t) (Mop P Z t c)) = Mop P Z t c ∧
    Matrix.toEuclideanLin (Sinf P Z t) c =
      Matrix.toEuclideanLin (J₀ n) (Zinv (Z t) (Mop P Z t c)) := by
  have h1 := Z_Zinv hZ t _ (F2 hH hZ t c)
  refine ⟨h1, ?_⟩
  ext i
  rw [S_apply hH hZ, ← fr_coord hZ, h1]

lemma S_symm (t : ℝ) : (Sinf P Z t).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Sinf, Matrix.of_apply, Mop, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, om_sub_left, om_smul_left]
  have h4 := F4 hZ t (e i) (e j)
  have hs := skew hH P (P.T * t) (Z t (e i)) (Z t (e j)) ((hZ.2.2 t).1 _) ((hZ.2.2 t).1 _)
  have a1 := om_antisymm (Z t (e i)) (deriv Z t (e j))
  have a2 := om_antisymm (Z t (e i)) (Aop P t (Z t (e j)))
  simp only [Aop] at *
  have k1 : omega0 ((deriv Z t) (e i)) ((Z t) (e j)) = omega0 ((deriv Z t) (e j)) ((Z t) (e i)) := by
    linarith
  have k2 : omega0 ((fderiv ℝ (reeb H) (P.x (P.T * t))) ((Z t) (e i))) ((Z t) (e j)) =
      omega0 ((fderiv ℝ (reeb H) (P.x (P.T * t))) ((Z t) (e j))) ((Z t) (e i)) := by linarith
  rw [k1, k2]

end frame3


lemma lin_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ → E →L[ℝ] E}
    (hL : Continuous L) {f g : ℝ → E} (hf : ∀ t, HasDerivAt f (L t (f t)) t)
    (hg : ∀ t, HasDerivAt g (L t (g t)) t) (h0 : f 0 = g 0) : f 1 = g 1 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hL.continuousOn
  have hv : ∀ t ∈ Ico (0 : ℝ) 1, LipschitzOnWith C.toNNReal (L t) univ := by
    intro t ht
    refine ((L t).lipschitz.weaken ?_).lipschitzOnWith
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact le_max_of_le_left (hC t (Ico_subset_Icc_self ht))
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  exact ODE_solution_unique_of_mem_Icc_right hv hfc.continuousOn
    (fun t _ => (hf t).hasDerivWithinAt) (fun _ _ => trivial) hgc.continuousOn
    (fun t _ => (hg t).hasDerivWithinAt) (fun _ _ => trivial) h0 ⟨zero_le_one, le_rfl⟩

lemma mat_rep (M : Mat n) (a : Vec n) :
    Matrix.toEuclideanLin M a = ∑ i, (∑ j, M i j * a j) • e i := by
  rw [vec_expand (Matrix.toEuclideanLin M a)]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

lemma mat_deriv {Ψ : ℝ → Mat n} {Ψ' : Mat n} {t : ℝ} (h : HasDerivAt Ψ Ψ' t) (a : Vec n) :
    HasDerivAt (fun s => Matrix.toEuclideanLin (Ψ s) a) (Matrix.toEuclideanLin Ψ' a) t := by
  simp only [mat_rep]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.smul_const (HasDerivAt.fun_sum fun j _ => ?_) _
  exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j).mul_const _

section frame4
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V n → V n →L[ℝ] V n}
  {P : ReebOrbit H} {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z)
include hH hZ

lemma Mop_smooth : ContDiff ℝ ∞ (Mop P Z) := by
  have hdZ : ContDiff ℝ ∞ (deriv Z) := (contDiff_infty_iff_deriv.1 hZ.1).2
  exact hdZ.sub (((A_smooth hH P).clm_comp hZ.1).const_smul P.T)

lemma S_smooth (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun t => Sinf P Z t i j) := by
  have : (fun t => Sinf P Z t i j) = fun t => om (Mop P Z t (e j)) (Z t (e i)) := rfl
  rw [this]
  exact (om.contDiff.comp ((Mop_smooth hH hZ).clm_apply contDiff_const)).clm_apply
    (hZ.1.clm_apply contDiff_const)

lemma xT_periodic (t : ℝ) : P.x (P.T * (t + 1)) = P.x (P.T * t) := by
  rw [mul_add, mul_one]; exact P.periodic _

lemma S_periodic : Function.Periodic (Sinf P Z) 1 := by
  intro t
  have h1 : deriv Z (t + 1) = deriv Z t := by
    rw [← deriv_comp_add_const]; congr 1; funext s; exact hZ.2.1 s
  have h2 : Aop P (t + 1) = Aop P t := by simp only [Aop]; rw [xT_periodic hH hZ]
  have h3 : Mop P Z (t + 1) = Mop P Z t := by simp only [Mop, h1, h2, hZ.2.1 t]
  simp only [Sinf, h3, hZ.2.1 t]

/-- `Z J₀ S c = -M c` -/
lemma ZJS (t : ℝ) (c : Vec n) :
    Z t (Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (Sinf P Z t) c)) = -Mop P Z t c := by
  obtain ⟨h1, h2⟩ := S_eq hH hZ t c
  rw [h2, JJ, map_neg, h1]

lemma op_identity (η : ℝ → Vec n) (hη : ContDiff ℝ ∞ η) (t : ℝ) :
    asympOp J P (fun t => Z t (η t)) t =
      Z t (-(Matrix.toEuclideanLin (J₀ n) (deriv η t)) -
        Matrix.toEuclideanLin (Sinf P Z t) (η t)) := by
  have hd : deriv (fun t => Z t (η t)) t = deriv Z t (η t) + Z t (deriv η t) :=
    ((Zdiff hZ) t).hasDerivAt.clm_apply ((hη.differentiable (by simp)) t).hasDerivAt |>.deriv
  obtain ⟨h1, h2⟩ := S_eq hH hZ t (η t)
  set b := Zinv (Z t) (Mop P Z t (η t))
  have hin : -deriv (fun t => Z t (η t)) t + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (Z t (η t))
      = -(Z t (deriv η t)) - Z t b := by
    rw [hd, h1]; simp only [Mop, Aop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply]; abel
  simp only [asympOp]
  rw [hin, map_sub, map_neg, (hZ.2.2 t).2.2.1, (hZ.2.2 t).2.2.1, h2, map_sub, map_neg]

lemma nondeg_iff : P.IsNondegenerate ↔ CauchyRiemannIndex.IsNondegenerate (Sinf P Z) := by
  have hAc : Continuous fun t => P.T • Aop P t := by
    have := (A_smooth hH P).continuous; unfold Aop; fun_prop
  constructor
  · intro hP Ψ hΨ hdet
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    set av : Vec n := WithLp.toLp 2 a
    obtain ⟨Φ, hΦ, -⟩ := (linReebFlow_spec H hH P).1
    set v := Z 0 av
    have hv : IsInXi H (P.x 0) v := by
      have := (hZ.2.2 0).1 av; rwa [mul_zero] at this
    set f : ℝ → V n := fun t => Z t (Matrix.toEuclideanLin (Ψ t) av)
    set g : ℝ → V n := fun t => Φ (P.T * t) v
    have hf : ∀ t, HasDerivAt f ((P.T • Aop P t) (f t)) t := by
      intro t
      have h1 := ((Zdiff hZ) t).hasDerivAt.clm_apply (mat_deriv (hΨ.2 t) av)
      refine h1.congr_deriv ?_
      have e1 : Matrix.toEuclideanLin (J₀ n * Sinf P Z t * Ψ t) av =
          Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (Sinf P Z t)
            (Matrix.toEuclideanLin (Ψ t) av)) := by
        simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [e1, ZJS hH hZ]
      simp [Mop, f]
    have hg : ∀ t, HasDerivAt g ((P.T • Aop P t) (g t)) t := by
      intro t
      have h2 : HasDerivAt (fun s : ℝ => P.T * s) P.T t := by
        simpa using (hasDerivAt_id t).const_mul P.T
      have h3 := ((hΦ.2 (P.T * t)).scomp t h2).clm_apply (hasDerivAt_const t v)
      refine h3.congr_deriv ?_
      simp [Aop, g]
    have h01 := lin_unique hAc hf hg (by simp [f, g, hΨ.1, hΦ.1, v])
    have hfix : Φ P.T v = v := by
      have hΨ1 : Matrix.toEuclideanLin (Ψ 1) av = av := by
        have : Matrix.mulVec (1 - Ψ 1) a = a - Matrix.mulVec (Ψ 1) a := by simp [Matrix.sub_mulVec]
        rw [this, sub_eq_zero] at ha
        simp [Matrix.toEuclideanLin_apply, av, ← ha]
      have := h01.symm
      simp only [f, g, mul_one, hΨ1] at this
      rw [this, show (1 : ℝ) = 0 + 1 by norm_num, hZ.2.1 0]
    have := fr_inj hZ 0 av (hP Φ hΦ v hv hfix)
    exact ha0 (by simpa [av] using congrArg WithLp.ofLp this)
  · intro hS Φ hΦ v hv hfix
    have hsp := ((linReebFlow_spec H hH P).2 Φ hΦ).1
    -- the fundamental solution `Ψ(t) = Z(t)⁻¹ Φ(Tt) Z(0)`
    set Ψ : ℝ → Mat n := fun t => Matrix.of fun i j =>
      Zinv (Z t) (Φ (P.T * t) (Z 0 (e j))) i
    have hZ0 : ∀ b, IsInXi H (P.x 0) (Z 0 b) := fun b => by
      have := (hZ.2.2 0).1 b; rwa [mul_zero] at this
    have hY : ∀ t b, IsInXi H (P.x (P.T * t)) (Φ (P.T * t) (Z 0 b)) := fun t b =>
      (hsp (P.T * t) _ _ (hZ0 b) (hZ0 b)).1
    have hΨc : ∀ t (b : Vec n), Matrix.toEuclideanLin (Ψ t) b = Zinv (Z t) (Φ (P.T * t) (Z 0 b)) := by
      intro t b
      rw [mat_rep]
      conv_rhs => rw [vec_expand (Zinv (Z t) (Φ (P.T * t) (Z 0 b))), vec_expand b]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [map_sum, map_smul, Ψ, Matrix.of_apply]
      simp [Finset.sum_apply, mul_comm]
    have hΨ : CauchyRiemannIndex.IsFundamentalSolution (Sinf P Z) Ψ := by
      refine ⟨?_, fun t => ?_⟩
      · ext i j
        simp [Ψ, hΦ.1, Zinv_Z hZ, Matrix.one_apply, e, EuclideanSpace.single_apply, eq_comm]
      · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
        -- column `j`: `c(t) = Z(t)⁻¹ Y(t)` with `Y(t) = Φ(Tt) Z(0) eⱼ`
        set Y : ℝ → V n := fun s => Φ (P.T * s) (Z 0 (e j))
        have hYd : HasDerivAt Y ((P.T • Aop P t) (Y t)) t := by
          have h2 : HasDerivAt (fun s : ℝ => P.T * s) P.T t := by
            simpa using (hasDerivAt_id t).const_mul P.T
          have h3 := ((hΦ.2 (P.T * t)).scomp t h2).clm_apply (hasDerivAt_const t (Z 0 (e j)))
          refine h3.congr_deriv ?_
          simp [Aop, Y]
        set c := Zinv (Z t) (Y t)
        have hc : Z t c = Y t := Z_Zinv hZ t _ (hY t _)
        -- `Ψ s i j = -(J₀ (coord))ᵢ`, differentiate the coordinates `ω₀(Y, Z eₖ)`
        have hk : ∀ k, HasDerivAt (fun s => omega0 (Y s) (Z s (e k)))
            (-(Matrix.toEuclideanLin (Sinf P Z t) c k)) t := by
          intro k
          have hz : HasDerivAt (fun s => Z s (e k)) (deriv Z t (e k)) t := by
            simpa using ((Zdiff hZ) t).hasDerivAt.clm_apply (hasDerivAt_const t (e k))
          refine (hasDerivAt_om hYd hz).congr_deriv ?_
          rw [S_apply hH hZ, ← hc]
          have h4 := F4 hZ t c (e k)
          simp only [Mop, Aop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.comp_apply, om_sub_left, om_smul_left] at h4 ⊢
          linarith
        have hrep : (fun s => Ψ s i j) = fun s =>
            -∑ k, J₀ n i k * omega0 (Y s) (Z s (e k)) := by
          funext s
          simp [Ψ, Zinv, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, coordL_apply, Y]
        rw [hrep]
        refine (HasDerivAt.fun_sum (fun k _ => (hk k).const_mul (J₀ n i k))).neg.congr_deriv ?_
        -- compare with `(J₀ S Ψ)ᵢⱼ`
        have hcol : (fun k => Ψ t k j) = WithLp.ofLp c := by
          funext k; simp [Ψ, c, Y]
        have : (J₀ n * Sinf P Z t * Ψ t) i j =
            (Matrix.mulVec (J₀ n) (Matrix.mulVec (Sinf P Z t) (WithLp.ofLp c))) i := by
          rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
        rw [this]
        simp only [Matrix.toEuclideanLin_apply, PiLp.toLp_apply, mul_neg, Finset.sum_neg_distrib,
          neg_neg]
        rfl
    have hdet := hS Ψ hΨ
    set a := Zinv (Z 0) v
    have hZa : Z 0 a = v := Z_Zinv hZ 0 v (by rw [mul_zero]; exact hv)
    have hΨ1 : Matrix.toEuclideanLin (Ψ 1) a = a := by
      rw [hΨc, mul_one, hZa, hfix, show (1 : ℝ) = 0 + 1 by norm_num, hZ.2.1 0]
    have hker : Matrix.mulVec (1 - Ψ 1) (WithLp.ofLp a) = 0 := by
      have := congrArg WithLp.ofLp hΨ1
      simp only [Matrix.toEuclideanLin_apply] at this
      simp [Matrix.sub_mulVec, this]
    by_contra hv0
    have ha0 : WithLp.ofLp a ≠ 0 := by
      intro h0
      have : a = 0 := by ext i; rw [h0]; rfl
      rw [this, map_zero] at hZa
      exact hv0 hZa.symm
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, ha0, hker⟩)

end frame4

end FrameBridge

open FrameBridge in
theorem solution_core {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (hex : ∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z) :
    (∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z) ∧
      ∀ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z →
        ∃ Sinf : ℝ → CauchyRiemannIndex.Mat n, CauchyRiemannIndex.IsSymLoop Sinf ∧
          (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
          (∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
            ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
              Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
                Matrix.toEuclideanLin (Sinf t) (η t))) ∧
          (P.IsNondegenerate ↔ CauchyRiemannIndex.IsNondegenerate Sinf) := by
  refine ⟨hex, fun Z hZ => ⟨Sinf P Z, ⟨?_, S_periodic hH hZ, S_symm hH hZ⟩, S_smooth hH hZ,
    fun η hη _ t => op_identity hH hZ η hη t, nondeg_iff hH hZ⟩⟩
  exact continuous_pi fun i => continuous_pi fun j => (S_smooth hH hZ i j).continuous

open FiniteEnergyPlane in
theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    (∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z) ∧
      ∀ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z →
        ∃ Sinf : ℝ → CauchyRiemannIndex.Mat n, CauchyRiemannIndex.IsSymLoop Sinf ∧
          (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
          (∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
            ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
              Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
                Matrix.toEuclideanLin (Sinf t) (η t))) ∧
          (P.IsNondegenerate ↔ CauchyRiemannIndex.IsNondegenerate Sinf) :=
  solution_core H hH J hJ P (exists_unitaryXiFrame H hH J hJ P)
