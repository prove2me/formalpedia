-- Prove2me | solution 1 for ClarkeGradients.FlowInvariance.flowInvariant_iff_subset_tangentCone
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T23:40:09.325067+00:00
-- url     : https://prove2.me/submissions/4037888c-266b-47cb-a925-c89fcb828d2e

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_tangentCone
import Definitions.Def_ClarkeGradients_FlowInvariance_IsLipschitzMultifunction
import Definitions.Def_ClarkeGradients_FlowInvariance_FlowInvariant
import Definitions.Def_ClarkeGradients_FlowInvariance_IsTrajectory

set_option autoImplicit false

/- Complete checked body: EulerTracking -/
section

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace ClarkeGradients.FlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasMultifunctionBound (X : E → Set E) (K : ℝ) : Prop :=
  ∀ x y, ∀ v ∈ X x, ∃ w ∈ X y, ‖v - w‖ ≤ K * ‖x - y‖

structure EulerMesh (X : E → Set E) (h : ℝ) (x₀ v₀ : E) where
  pos : ℕ → E
  vel : ℕ → E
  pos_zero : pos 0 = x₀
  vel_zero : vel 0 = v₀
  vel_mem : ∀ j, vel j ∈ X (pos j)
  pos_succ : ∀ j, pos (j + 1) = pos j + h • vel j

theorem exists_euler_mesh (X : E → Set E) {K h : ℝ}
    (hX : HasMultifunctionBound X K) {x₀ v₀ : E} (hv : v₀ ∈ X x₀) :
    ∃ u : EulerMesh X h x₀ v₀, ∀ j,
      ‖u.vel (j + 1) - u.vel j‖ ≤ K * |h| * ‖u.vel j‖ := by
  classical
  let S := {z : E × E // z.2 ∈ X z.1}
  let next : S → S := fun z =>
    ⟨(z.1.1 + h • z.1.2, (hX z.1.1 (z.1.1 + h • z.1.2) z.1.2 z.2).choose),
      (hX z.1.1 (z.1.1 + h • z.1.2) z.1.2 z.2).choose_spec.1⟩
  have next_bound (z : S) : ‖(next z).1.2-z.1.2‖ ≤ K * |h| * ‖z.1.2‖ := by
    change ‖(hX z.1.1 (z.1.1+h • z.1.2) z.1.2 z.2).choose-z.1.2‖ ≤ _
    rw [norm_sub_rev]
    calc
      _ ≤ K*‖z.1.1-(z.1.1+h • z.1.2)‖ :=
        (hX z.1.1 (z.1.1+h • z.1.2) z.1.2 z.2).choose_spec.2
      _ = _ := by simp only [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg,
        norm_smul,Real.norm_eq_abs,mul_assoc]
  let seq : ℕ → S := fun j => next^[j] ⟨(x₀, v₀), hv⟩
  have hs (j : ℕ) : seq (j + 1) = next (seq j) := by
    exact Function.iterate_succ_apply' next j _
  let u : EulerMesh X h x₀ v₀ :=
    { pos := fun j => (seq j).1.1
      vel := fun j => (seq j).1.2
      pos_zero := rfl
      vel_zero := rfl
      vel_mem := fun j => (seq j).2
      pos_succ := fun j => congrArg (fun z : S => z.1.1) (hs j) }
  refine ⟨u, fun j => ?_⟩
  change ‖(seq (j + 1)).1.2 - (seq j).1.2‖ ≤ K * |h| * ‖(seq j).1.2‖
  rw [hs]
  exact next_bound (seq j)

theorem euler_velocity_exp_bound {X : E → Set E} {K h : ℝ}
    (_hK : 0 ≤ K) (_hh : 0 ≤ h) {x₀ v₀ : E} (u : EulerMesh X h x₀ v₀)
    (hstep : ∀ j, ‖u.vel (j + 1) - u.vel j‖ ≤ K * h * ‖u.vel j‖) :
    ∀ j, ‖u.vel j‖ ≤ Real.exp (K * ((j : ℝ) * h)) * ‖v₀‖ := by
  intro j
  induction j with
  | zero => simp [u.vel_zero]
  | succ j ih =>
    have hrec : ‖u.vel (j+1)‖ ≤ (1 + K*h) * ‖u.vel j‖ := by
      have := norm_add_le (u.vel (j+1)-u.vel j) (u.vel j)
      rw [sub_add_cancel] at this
      nlinarith [hstep j]
    calc
      ‖u.vel (j+1)‖ ≤ (1+K*h)*‖u.vel j‖ := hrec
      _ ≤ Real.exp (K*h) * (Real.exp (K*((j:ℝ)*h))*‖v₀‖) := by
        apply mul_le_mul
        · simpa [add_comm] using Real.add_one_le_exp (K*h)
        · exact ih
        · exact norm_nonneg _
        · positivity
      _ = Real.exp (K*(((j+1:ℕ):ℝ)*h))*‖v₀‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring

theorem euler_velocity_bound {X : E → Set E} {K h : ℝ}
    (hK : 0 ≤ K) (hh : 0 ≤ h) {x₀ v₀ : E} (u : EulerMesh X h x₀ v₀)
    (hstep : ∀ j, ‖u.vel (j+1)-u.vel j‖ ≤ K*h*‖u.vel j‖)
    {j : ℕ} (hj : (j:ℝ)*h ≤ 1) :
    ‖u.vel j‖ ≤ Real.exp K * ‖v₀‖ := by
  apply (euler_velocity_exp_bound hK hh u hstep j).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem euler_velocity_dist_le {X : E → Set E} {K h C : ℝ}
    (hK : 0 ≤ K) (hh : 0 ≤ h) {x₀ v₀ : E} (u : EulerMesh X h x₀ v₀)
    (hstep : ∀ j, ‖u.vel (j+1)-u.vel j‖ ≤ K*h*‖u.vel j‖)
    {N i j : ℕ} (hb : ∀ k ≤ N, ‖u.vel k‖ ≤ C) (hi : i ≤ N) (hj : j ≤ N) :
    dist (u.vel i) (u.vel j) ≤ K*C*dist ((i:ℝ)*h) ((j:ℝ)*h) := by
  have ordered {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N) :
      dist (u.vel a) (u.vel b) ≤ K*C*(((b:ℝ)-(a:ℝ))*h) := by
    calc
      dist (u.vel a) (u.vel b) ≤ ∑ k ∈ Finset.Ico a b, K*h*C := by
        apply dist_le_Ico_sum_of_dist_le hab
        intro k _ hk
        rw [dist_eq_norm, norm_sub_rev]
        exact (hstep k).trans (mul_le_mul_of_nonneg_left (hb k (by omega)) (by positivity))
      _ = K*C*(((b:ℝ)-(a:ℝ))*h) := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          Nat.cast_sub hab]
        ring
  rcases le_total i j with hij | hji
  · have hij' : (i:ℝ)*h ≤ (j:ℝ)*h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hij')]
    calc
      _ ≤ K*C*(((j:ℝ)-(i:ℝ))*h) := ordered hij hj
      _ = _ := by ring
  · rw [dist_comm, dist_comm ((i:ℝ)*h)]
    have hji' : (j:ℝ)*h ≤ (i:ℝ)*h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hji) hh
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hji')]
    calc
      _ ≤ K*C*(((i:ℝ)-(j:ℝ))*h) := ordered hji hi
      _ = _ := by ring

end ClarkeGradients.FlowProof

end

/- Complete checked body: GridExtension -/
section

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace ClarkeGradients.FlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finite_grid_extension (v : ℕ → E) {N : ℕ} {h : ℝ} (hh : 0 < h)
    (L : ℝ≥0)
    (hv : ∀ i ≤ N, ∀ j ≤ N,
      dist (v i) (v j) ≤ L * dist ((i:ℝ)*h) ((j:ℝ)*h)) :
    ∃ g : ℝ → E, LipschitzWith (lipschitzExtensionConstant E * L) g ∧
      ∀ i ≤ N, g ((i:ℝ)*h) = v i := by
  classical
  let τ : Fin (N+1) → ℝ := fun i => (i:ℝ)*h
  have hτ : Function.Injective τ := by
    intro i j hij
    apply Fin.ext
    have := (mul_right_cancel₀ hh.ne' hij : (i:ℝ)=(j:ℝ))
    exact_mod_cast this
  let f : ℝ → E := Function.extend τ (fun i : Fin (N+1) => v i) (fun _ => 0)
  have hf : LipschitzOnWith L f (range τ) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩
    simp only [f, hτ.extend_apply]
    exact hv i (by omega) j (by omega)
  obtain ⟨g,hg,heq⟩ := hf.extend_finite_dimension
  refine ⟨g,hg,fun i hi => ?_⟩
  let j : Fin (N+1) := ⟨i,by omega⟩
  have he := heq (mem_range_self j)
  simpa only [f,hτ.extend_apply,τ] using he.symm

theorem exists_extended_euler (X : E → Set E) (K : ℝ≥0)
    (hX : HasMultifunctionBound X K) (x₀ v₀ : E) (hv : v₀ ∈ X x₀)
    (N : ℕ) (hN : 0 < N) :
    ∃ (u : EulerMesh X (1/(N:ℝ)) x₀ v₀) (g : ℝ → E),
      LipschitzWith (lipschitzExtensionConstant E *
        ⟨(K:ℝ)*(Real.exp K*‖v₀‖),by positivity⟩) g ∧
      (∀ i ≤ N, g ((i:ℝ)/(N:ℝ)) = u.vel i) ∧
      ∀ i ≤ N, ‖u.vel i‖ ≤ Real.exp K*‖v₀‖ := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨u,hu⟩ := exists_euler_mesh X hX hv (h := 1/(N:ℝ))
  have hu' : ∀ j, ‖u.vel (j+1)-u.vel j‖ ≤ (K:ℝ)*(1/(N:ℝ))*‖u.vel j‖ := by
    simpa only [abs_of_pos (one_div_pos.mpr hn)] using hu
  have hb (i : ℕ) (hi : i ≤ N) : ‖u.vel i‖ ≤ Real.exp K*‖v₀‖ := by
    apply euler_velocity_bound K.coe_nonneg (by positivity) u hu'
    rw [mul_one_div, div_le_one hn]
    exact_mod_cast hi
  obtain ⟨g,hg,hgv⟩ := finite_grid_extension u.vel (one_div_pos.mpr hn)
    ⟨(K:ℝ)*(Real.exp K*‖v₀‖),by positivity⟩
    (fun i hi j hj => euler_velocity_dist_le K.coe_nonneg (by positivity) u hu' hb hi hj)
  exact ⟨u,g,hg,by simpa only [mul_one_div] using hgv,hb⟩

end ClarkeGradients.FlowProof

end

/- Complete checked body: EulerIntegrals -/
section

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology NNReal

namespace ClarkeGradients.FlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def integratedPath (x₀ : E) (g : ℝ → E) (t : ℝ) : E :=
  x₀ + ∫ s in (0:ℝ)..t, g s

omit [CompleteSpace E] in
theorem integratedPath_sub (x₀ : E) {g : ℝ → E} (hg : Continuous g) (a b : ℝ) :
    integratedPath x₀ g b - integratedPath x₀ g a = ∫ s in a..b, g s := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (0:ℝ) a) (hg.intervalIntegrable a b)
  simp only [integratedPath]
  rw [← h]
  abel

theorem integral_euler_cell {g : ℝ → E} {L : ℝ≥0} (hg : LipschitzWith L g)
    {a b : ℝ} (hab : a ≤ b) :
    ‖(∫ s in a..b, g s) - (b-a) • g a‖ ≤ (L:ℝ)*(b-a)^2 := by
  have heq : (∫ s in a..b, g s) - (b-a) • g a = ∫ s in a..b, g s-g a := by
    rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable a b)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => g a) volume a b),
      intervalIntegral.integral_const]
  rw [heq]
  calc
    ‖∫ s in a..b, g s-g a‖ ≤ ((L:ℝ)*(b-a))*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hab] at hs
      have h := hg.dist_le_mul s a
      rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1.le)] at h
      exact h.trans (by nlinarith [L.coe_nonneg,hs.2])
    _ = (L:ℝ)*(b-a)^2 := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring

theorem euler_grid_error {X : E → Set E} {h : ℝ} (hh : 0 ≤ h)
    {x₀ v₀ : E} (u : EulerMesh X h x₀ v₀) {g : ℝ → E} {L : ℝ≥0}
    (hg : LipschitzWith L g) {N : ℕ}
    (hmatch : ∀ i ≤ N, g ((i:ℝ)*h) = u.vel i) :
    ∀ j ≤ N, ‖integratedPath x₀ g ((j:ℝ)*h)-u.pos j‖ ≤ (j:ℝ)*(L:ℝ)*h^2 := by
  intro j hj
  induction j with
  | zero => simp [integratedPath,u.pos_zero]
  | succ j ih =>
    have hjN : j ≤ N := by omega
    have hcell := integral_euler_cell hg
      (show (j:ℝ)*h ≤ ((j+1:ℕ):ℝ)*h by push_cast; nlinarith)
    have hlen : ((j+1:ℕ):ℝ)*h-(j:ℝ)*h=h := by push_cast; ring
    rw [hlen,hmatch j hjN] at hcell
    have hdecomp : integratedPath x₀ g (((j+1:ℕ):ℝ)*h)-u.pos (j+1) =
        (integratedPath x₀ g ((j:ℝ)*h)-u.pos j) +
        ((∫ s in (j:ℝ)*h..((j+1:ℕ):ℝ)*h, g s)-h • u.vel j) := by
      rw [← integratedPath_sub x₀ hg.continuous,u.pos_succ]
      abel
    rw [hdecomp]
    have hn := norm_add_le (integratedPath x₀ g ((j:ℝ)*h)-u.pos j)
      ((∫ s in (j:ℝ)*h..((j+1:ℕ):ℝ)*h, g s)-h • u.vel j)
    have hi := ih hjN
    push_cast at hcell hn ⊢
    nlinarith

omit [CompleteSpace E] in
theorem integratedPath_norm_sub_le {g : ℝ → E} (hg : Continuous g) (x₀ : E)
    {a b C : ℝ} (hab : a ≤ b) (hb : ∀ s ∈ Icc a b, ‖g s‖ ≤ C) :
    ‖integratedPath x₀ g b-integratedPath x₀ g a‖ ≤ C*(b-a) := by
  rw [integratedPath_sub x₀ hg]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
    intervalIntegral.norm_integral_le_of_norm_le_const (f := g) (a := a) (b := b)
      (fun s hs => hb s (by rw [uIoc_of_le hab] at hs; exact ⟨hs.1.le,hs.2⟩))

theorem euler_near_node {X : E → Set E} {N : ℕ} (hN : 0 < N)
    {x₀ v₀ : E} (u : EulerMesh X (1/(N:ℝ)) x₀ v₀)
    {g : ℝ → E} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hmatch : ∀ i ≤ N, g ((i:ℝ)/(N:ℝ))=u.vel i)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i ≤ N, ‖u.vel i‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ i ≤ N, ‖g t-u.vel i‖ ≤ (L:ℝ)/(N:ℝ) ∧
      ‖integratedPath x₀ g t-u.pos i‖ ≤ (C+2*(L:ℝ))/(N:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  let i := ⌊t*(N:ℝ)⌋₊
  have hi0 : (i:ℝ) ≤ t*(N:ℝ) := Nat.floor_le (mul_nonneg ht.1 hn.le)
  have hi1 : t*(N:ℝ) < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have hiN : i ≤ N := by
    have : (i:ℝ) ≤ N := hi0.trans (by nlinarith [ht.2])
    exact_mod_cast this
  let a : ℝ := (i:ℝ)/(N:ℝ)
  have hat : a ≤ t := (div_le_iff₀ hn).2 hi0
  have hgap : t-a ≤ 1/(N:ℝ) := by
    apply (le_div_iff₀ hn).2
    dsimp [a]
    field_simp
    nlinarith
  have hv : ‖g t-u.vel i‖ ≤ (L:ℝ)/(N:ℝ) := by
    rw [← hmatch i hiN]
    have h := hg.dist_le_mul t a
    rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hat)] at h
    exact h.trans (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hgap L.coe_nonneg)
  refine ⟨i,hiN,hv,?_⟩
  have hgb : ∀ s ∈ Icc a t, ‖g s‖ ≤ C+(L:ℝ)/(N:ℝ) := by
    intro s hs
    have hd := hg.dist_le_mul s a
    rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hs.1)] at hd
    have hgn := norm_add_le (g s-g a) (g a)
    rw [sub_add_cancel] at hgn
    have hga : ‖g a‖ ≤ C := by dsimp [a]; rw [hmatch i hiN]; exact hb i hiN
    have hsGap : s-a ≤ 1/(N:ℝ) := (sub_le_sub_right hs.2 a).trans hgap
    have hd' : (L:ℝ)*(s-a) ≤ (L:ℝ)/(N:ℝ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsGap L.coe_nonneg
    linarith
  have hpart := integratedPath_norm_sub_le hg.continuous x₀ hat hgb
  have hgrid := euler_grid_error (by positivity) u hg
    (by simpa only [mul_one_div] using hmatch) i hiN
  have hgrid' : ‖integratedPath x₀ g a-u.pos i‖ ≤ (L:ℝ)/(N:ℝ) := by
    calc
      _ ≤ (i:ℝ)*(L:ℝ)*(1/(N:ℝ))^2 := by
        simpa only [a,mul_one_div] using hgrid
      _ = ((i:ℝ)/(N:ℝ))*((L:ℝ)/(N:ℝ)) := by ring
      _ ≤ 1*((L:ℝ)/(N:ℝ)) := mul_le_mul_of_nonneg_right
        ((div_le_one hn).2 (by exact_mod_cast hiN)) (by positivity)
      _ = _ := one_mul _

  have hLdiv : (L:ℝ)/(N:ℝ) ≤ L := (div_le_self L.coe_nonneg hn1)
  have hp : ‖integratedPath x₀ g t-integratedPath x₀ g a‖ ≤ (C+(L:ℝ))/(N:ℝ) := by
    apply hpart.trans
    calc
      (C+(L:ℝ)/(N:ℝ))*(t-a) ≤ (C+(L:ℝ))*(1/(N:ℝ)) :=
        mul_le_mul (by linarith) hgap (sub_nonneg.mpr hat) (by positivity)
      _ = (C+(L:ℝ))/(N:ℝ) := by ring
  have htri := norm_add_le
    (integratedPath x₀ g t-integratedPath x₀ g a)
    (integratedPath x₀ g a-u.pos i)
  rw [sub_add_sub_cancel] at htri
  calc
    _ ≤ (C+(L:ℝ))/(N:ℝ)+(L:ℝ)/(N:ℝ) := htri.trans (add_le_add hp hgrid')
    _ = _ := by ring

end ClarkeGradients.FlowProof

end

/- Complete checked body: VelocityCompactness -/
section

set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal BoundedContinuousFunction

namespace ClarkeGradients.FlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem velocity_subsequence (g : ℕ → ℝ → E) (L : ℝ≥0) (v₀ : E)
    (hg : ∀ j, LipschitzWith L (g j)) (hzero : ∀ j, g j 0 = v₀) :
    ∃ (v : ℝ → E) (φ : ℕ → ℕ) (err : ℕ → ℝ),
      Continuous v ∧ v 0 = v₀ ∧ StrictMono φ ∧ Tendsto err atTop (𝓝 0) ∧
      (∀ j, 0 ≤ err j) ∧
      ∀ j t, t ∈ Icc (0:ℝ) 1 → ‖g (φ j) t - v t‖ ≤ err j := by
  classical
  let I := Icc (0:ℝ) 1
  let G : ℕ → (I →ᵇ E) := fun j =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t => g j t, (hg j).continuous.comp continuous_subtype_val⟩
  have hG (j : ℕ) : LipschitzWith L (G j) := by
    change LipschitzWith L (fun t : I => g j (t:ℝ))
    simpa only [mul_one,Function.comp_def] using (hg j).comp (LipschitzWith.subtype_val I)
  have hrange (f : I →ᵇ E) (t : I) (hf : f ∈ range G) :
      f t ∈ closedBall v₀ L := by
    rcases hf with ⟨j,rfl⟩
    rw [mem_closedBall]
    change dist (g j (t:ℝ)) v₀ ≤ L
    rw [← hzero j]
    have h := (hg j).dist_le_mul (t:ℝ) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.2.1] at h
    exact h.trans (by nlinarith [t.2.2, L.coe_nonneg])
  have hequi : Equicontinuous ((↑) : range G → I → E) := by
    apply (LipschitzWith.uniformEquicontinuous _ L ?_).equicontinuous
    intro f
    rcases f.2 with ⟨j,hj⟩
    simpa only [← hj] using hG j
  have hc := BoundedContinuousFunction.arzela_ascoli (closedBall v₀ L)
    (isCompact_closedBall v₀ L) (range G) hrange hequi
  obtain ⟨w, _hw, φ, hφ, hconv⟩ := hc.tendsto_subseq
    (fun j => subset_closure (mem_range_self j))
  let v : ℝ → E := fun t => w (projIcc 0 1 (by norm_num) t)
  let err : ℕ → ℝ := fun j => dist (G (φ j)) w
  have herr : Tendsto err atTop (𝓝 0) := by
    change Tendsto (fun j => dist (G (φ j)) w) atTop (𝓝 0)
    simpa only [Function.comp_apply,dist_self] using hconv.dist (tendsto_const_nhds (x := w))
  have hbound (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖g (φ j) t - v t‖ ≤ err j := by
    have h := BoundedContinuousFunction.dist_coe_le_dist (f := G (φ j)) (g := w) (⟨t,ht⟩ : I)
    change dist (g (φ j) t) (w ⟨t,ht⟩) ≤ err j at h
    simpa only [v,projIcc_of_mem _ ht,dist_eq_norm] using h

  have hinit : v 0 = v₀ := by
    have heq : ‖v₀ - v 0‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      apply ge_of_tendsto herr
      exact Eventually.of_forall (fun j => by simpa only [hzero] using hbound j 0 (by norm_num))
    exact (sub_eq_zero.mp (norm_eq_zero.mp heq)).symm
  exact ⟨v,φ,err,w.continuous.comp continuous_projIcc,hinit,hφ,herr,
    fun j => dist_nonneg,hbound⟩

end ClarkeGradients.FlowProof

end

/- Complete checked body: TrajectoryLimit -/
section

set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped Topology NNReal

namespace ClarkeGradients.FlowProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem integratedPath_uniform_le (x₀ : E) {g v : ℝ → E}
    (hg : Continuous g) (hv : Continuous v) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖g t-v t‖ ≤ ε) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖integratedPath x₀ g t-integratedPath x₀ v t‖ ≤ ε := by
  have heq : integratedPath x₀ g t-integratedPath x₀ v t =
      ∫ s in (0:ℝ)..t, g s-v s := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
    simp only [integratedPath]
    abel
  rw [heq]
  have h : ‖∫ s in (0:ℝ)..t, g s-v s‖ ≤ ε*|t-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact hb s ⟨hs.1.le,hs.2.trans ht.2⟩
  rw [sub_zero,abs_of_nonneg ht.1] at h
  exact h.trans (by nlinarith [ht.2])

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem multifunction_closed_graph {X : E → Set E} {K : ℝ}
    (hX : HasMultifunctionBound X K) (hclosed : ∀ x, IsClosed (X x))
    {z w : ℕ → E} {x v : E} (hz : Tendsto z atTop (𝓝 x))
    (hw : Tendsto w atTop (𝓝 v)) (hmem : ∀ j, w j ∈ X (z j)) : v ∈ X x := by
  classical
  choose q hq hdist using fun j => hX (z j) x (w j) (hmem j)
  have hqv : Tendsto q atTop (𝓝 v) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun j => norm_nonneg _)
      (fun j => show ‖q j-v‖ ≤ K*‖z j-x‖+‖w j-v‖ from
        (norm_sub_le_norm_sub_add_norm_sub (q j) (w j) v).trans (add_le_add
          (by simpa only [norm_sub_rev] using hdist j) le_rfl))
    simpa only [sub_self,norm_zero,mul_zero,add_zero] using
      ((tendsto_const_nhds (x := K)).mul ((hz.sub (tendsto_const_nhds (x := x))).norm)).add
        ((hw.sub (tendsto_const_nhds (x := v))).norm)
  exact (hclosed x).mem_of_tendsto hqv (Eventually.of_forall hq)

theorem integratedPath_hasDerivAt (x₀ : E) {v : ℝ → E} (hv : Continuous v) (t : ℝ) :
    HasDerivAt (integratedPath x₀ v) (v t) t := by
  exact (hv.integral_hasStrictDerivAt (0:ℝ) t).hasDerivAt.const_add x₀

theorem integratedPath_contDiff (x₀ : E) {v : ℝ → E} (hv : Continuous v) :
    ContDiff ℝ 1 (integratedPath x₀ v) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (integratedPath_hasDerivAt x₀ hv t).differentiableAt,?_⟩
  have heq : deriv (integratedPath x₀ v) = v :=
    funext (fun t => (integratedPath_hasDerivAt x₀ hv t).deriv)
  rwa [heq]

variable [FiniteDimensional ℝ E]

theorem exists_continuous_solution (X : E → Set E) (K : ℝ≥0)
    (hX : HasMultifunctionBound X K) (hclosed : ∀ x, IsClosed (X x))
    (x₀ v₀ : E) (hv₀ : v₀ ∈ X x₀) :
    ∃ v : ℝ → E, Continuous v ∧ v 0=v₀ ∧
      ∀ t ∈ Icc (0:ℝ) 1, v t ∈ X (integratedPath x₀ v t) := by
  classical
  let C : ℝ := Real.exp K*‖v₀‖
  let L : ℝ≥0 := lipschitzExtensionConstant E * ⟨(K:ℝ)*C,by dsimp [C]; positivity⟩
  choose u g hg hmatch hb using
    fun j : ℕ => exists_extended_euler X K hX x₀ v₀ hv₀ (j+1) (by omega)
  have hgL : ∀ j, LipschitzWith L (g j) := hg
  have hzero (j : ℕ) : g j 0=v₀ := by
    have h := hmatch j 0 (Nat.zero_le _)
    simpa only [Nat.cast_zero,zero_div,(u j).vel_zero] using h
  obtain ⟨v,φ,err,hv,hv0,hφ,herr,herr0,hbound⟩ := velocity_subsequence g L v₀ hgL hzero
  refine ⟨v,hv,hv0,fun t ht => ?_⟩
  choose i _hi hiv hiz using fun j : ℕ =>
    euler_near_node (by omega) (u (φ j)) (hgL (φ j)) (hmatch (φ j))
      (show 0 ≤ C by dsimp [C]; positivity) (hb (φ j)) ht
  have hmesh : Tendsto (fun j : ℕ => 1/(((φ j)+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have hpos : Tendsto (fun j => (u (φ j)).pos (i j)) atTop
      (𝓝 (integratedPath x₀ v t)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
      (show Tendsto (fun j => (C+2*(L:ℝ))*(1/(((φ j)+1:ℕ):ℝ))+err j)
        atTop (𝓝 0) by simpa using (tendsto_const_nhds.mul hmesh).add herr)
    have hp := integratedPath_uniform_le x₀ (hgL (φ j)).continuous hv (herr0 j) (hbound j) ht
    calc
      _ ≤ ‖(u (φ j)).pos (i j)-integratedPath x₀ (g (φ j)) t‖ +
          ‖integratedPath x₀ (g (φ j)) t-integratedPath x₀ v t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (C+2*(L:ℝ))/(((φ j)+1:ℕ):ℝ)+err j :=
        add_le_add (by simpa only [norm_sub_rev] using hiz j) hp
      _ = _ := by ring
  have hvel : Tendsto (fun j => (u (φ j)).vel (i j)) atTop (𝓝 (v t)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
      (show Tendsto (fun j => (L:ℝ)*(1/(((φ j)+1:ℕ):ℝ))+err j) atTop (𝓝 0) by
        simpa using (tendsto_const_nhds.mul hmesh).add herr)
    calc
      _ ≤ ‖(u (φ j)).vel (i j)-g (φ j) t‖+‖g (φ j) t-v t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (L:ℝ)/(((φ j)+1:ℕ):ℝ)+err j :=
        add_le_add (by simpa only [norm_sub_rev] using hiv j) (hbound j t ht)
      _ = _ := by ring
  exact multifunction_closed_graph hX hclosed hpos hvel (fun j => (u (φ j)).vel_mem (i j))

open ClarkeGradients.FlowInvariance

theorem exists_trajectory_initial {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x))
    (hLip : IsLipschitzMultifunction X) (x₀ v₀ : EuclideanSpace ℝ (Fin n))
    (hv₀ : v₀ ∈ X x₀) :
    ∃ x, IsTrajectory X x ∧ x 0=x₀ ∧ HasDerivAt x v₀ 0 := by
  obtain ⟨K,hK⟩ := hLip
  let L : ℝ≥0 := ⟨max K 0,le_max_right _ _⟩
  have hb : HasMultifunctionBound X L := by
    intro a b v hv
    obtain ⟨w,hw,hd⟩ := hK a b v hv
    exact ⟨w,hw,hd.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))⟩
  obtain ⟨v,hv,hv0,hmem⟩ := exists_continuous_solution X L hb
    (fun x => (hX x).2.isClosed) x₀ v₀ hv₀
  refine ⟨integratedPath x₀ v,⟨?_,?_⟩,?_,?_⟩
  · exact (integratedPath_contDiff x₀ hv).contDiffOn.absolutelyContinuousOnInterval
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨v t,hmem t ht,integratedPath_hasDerivAt x₀ hv t⟩
  · simp [integratedPath]
  · simpa only [hv0] using integratedPath_hasDerivAt x₀ hv 0

end ClarkeGradients.FlowProof

end

/- Complete checked body: AttributedGradient -/
section
-- Prove2me | solution 1 for ClarkeGradients.FlowInvariance.gradient_infDist_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:37:38.064932+00:00
-- url     : https://prove2.me/submissions/9aa9e3eb-06bf-41bf-86f3-5a785b3eb6d7


namespace ClarkeGradients.FlowInvariance

open InnerProductSpace RealInnerProductSpace

theorem aux_gid_inner {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient f x, v⟫_ℝ = fderiv ℝ f x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem aux_gid_norm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

theorem aux_gid_normle {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (fun y => Metric.infDist y E) x‖ ≤ 1 := by
  rw [aux_gid_norm]
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (Metric.lipschitz_infDist_pt (s := E))
  simpa using this

theorem aux_gid_dir {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (x e : EuclideanSpace ℝ (Fin n))
    (hdiff : DifferentiableAt ℝ (fun y => Metric.infDist y E) x)
    (he : e ∈ E) (hd : dist x e = Metric.infDist x E) (hxe : x ≠ e) :
    ‖x - e‖ ≤ fderiv ℝ (fun y => Metric.infDist y E) x (x - e) := by
  set f := fun y => Metric.infDist y E with hf
  set u := x - e with hu
  set d := ‖u‖ with hdd
  have hdpos : 0 < d := by
    rw [hdd, hu]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
  have hfx : f x = d := by
    simp only [hf, hdd, hu]; rw [← hd, dist_eq_norm]
  set F := fun y => d * f y - innerSL ℝ u y with hF
  have hderiv : HasFDerivAt F (d • fderiv ℝ f x - innerSL ℝ u) x :=
    (hdiff.hasFDerivAt.const_mul d).sub (innerSL ℝ u).hasFDerivAt
  have hmax : IsLocalMaxOn F (segment ℝ x e) x := by
    apply IsMaxOn.localize
    intro y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    simp only [Set.mem_ofPred_eq, hF]
    have h1 : f (a • x + b • e) ≤ a * d := by
      have := Metric.infDist_le_dist_of_mem (x := a • x + b • e) he
      refine this.trans (le_of_eq ?_)
      rw [dist_eq_norm]
      have : a • x + b • e - e = a • u := by
        rw [hu, smul_sub]
        have : b = 1 - a := by linarith
        subst this
        rw [sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_of_nonneg ha]
    have h2 : a • x + b • e = x - b • u := by
      have : a = 1 - b := by linarith
      subst this
      rw [hu, sub_smul, one_smul, smul_sub]; abel
    rw [h2, map_sub, map_smul, hfx]
    simp only [innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
    rw [← hdd]
    have : d * f (x - b • u) ≤ d * (a * d) := mul_le_mul_of_nonneg_left (h2 ▸ h1) hdpos.le
    nlinarith
  have hcone : e - x ∈ posTangentConeAt (segment ℝ x e) x :=
    sub_mem_posTangentConeAt_of_segment_subset (subset_refl _)
  have key := hmax.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt hcone
  have hex : e - x = -u := by rw [hu, neg_sub]
  rw [hex] at key
  simp only [sub_apply, smul_apply, map_neg,
    innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq] at key
  rw [← hdd] at key
  have : d * d ≤ d * fderiv ℝ f x u := by nlinarith
  exact le_of_mul_le_mul_left this hdpos

end ClarkeGradients.FlowInvariance

open ClarkeGradients.FlowInvariance

theorem checked_gradient_infDist_of_ne_zero {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : E.Nonempty) (hEc : IsClosed E) (x : EuclideanSpace ℝ (Fin n))
    (hdiff : DifferentiableAt ℝ (fun y => Metric.infDist y E) x)
    (hne : gradient (fun y => Metric.infDist y E) x ≠ 0) :
    x ∉ E ∧
      (∃! e : EuclideanSpace ℝ (Fin n), e ∈ E ∧ dist x e = Metric.infDist x E) ∧
      ∀ e ∈ E, dist x e = Metric.infDist x E →
        gradient (fun y => Metric.infDist y E) x = ‖x - e‖⁻¹ • (x - e) := by
  have hxE : x ∉ E := by
    intro hx
    apply hne
    have hmin : IsLocalMin (fun y => Metric.infDist y E) x := by
      apply Filter.Eventually.of_forall
      intro y
      simp only [Metric.infDist_zero_of_mem hx]
      exact Metric.infDist_nonneg
    have := hmin.fderiv_eq_zero
    simp [gradient, this]
  have hgrad : ∀ e ∈ E, dist x e = Metric.infDist x E →
      gradient (fun y => Metric.infDist y E) x = ‖x - e‖⁻¹ • (x - e) := by
    intro e he hd
    have hxe : x ≠ e := fun h => hxE (h ▸ he)
    have hdir := aux_gid_dir E x e hdiff he hd hxe
    rw [← aux_gid_inner] at hdir
    have hnorm := aux_gid_normle E x
    set g := gradient (fun y => Metric.infDist y E) x
    set u := x - e with hu
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
    set w := ‖u‖⁻¹ • u with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hupos.ne']
    have hgw : 1 ≤ inner ℝ g w := by
      rw [hw, inner_smul_right]
      rw [le_inv_mul_iff₀ hupos]; linarith
    have hsq : ‖g - w‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, hwn]
      have : ‖g‖ ^ 2 ≤ 1 := by
        have h0 := norm_nonneg g
        nlinarith
      nlinarith
    have : ‖g - w‖ = 0 := by
      have := sq_nonneg ‖g - w‖
      have h2 : ‖g - w‖ ^ 2 = 0 := le_antisymm hsq this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨hxE, ?_, hgrad⟩
  obtain ⟨e, he, hed⟩ := hEc.exists_infDist_eq_dist hE x
  refine ⟨e, ⟨he, hed.symm⟩, ?_⟩
  rintro e' ⟨he', hed'⟩
  have h1 := hgrad e he hed.symm
  have h2 := hgrad e' he' hed'
  rw [h1] at h2
  have hn : ‖x - e'‖ = ‖x - e‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, hed', hed]
  rw [hn] at h2
  have hxe : x ≠ e := fun h => hxE (h ▸ he)
  have hupos : 0 < ‖x - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
  have := smul_right_injective _ (inv_ne_zero hupos.ne') h2
  have : x - e' = x - e := this.symm
  exact sub_right_injective this

end

/- Complete checked body: ProximalGeometry -/
section

set_option autoImplicit false

open Filter Topology InnerProductSpace RealInnerProductSpace

namespace ClarkeGradients.FlowProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma proximal_pairing (F : Set E) (e u : E) (r : ℝ) (hr : 0 < r)
    (hu : ‖u‖ = 1) (hp : Metric.infDist (e + r • u) F = r)
    (z : E) (hz : z ∈ F) : 2 * r * inner ℝ u (z - e) ≤ ‖z - e‖ ^ 2 := by
  have hb := Metric.infDist_le_dist_of_mem (x := e + r • u) hz
  rw [hp, dist_eq_norm] at hb
  have he : e + r • u - z = r • u - (z - e) := by abel
  have hs : ‖e + r • u - z‖ ^ 2 = r ^ 2 + ‖z - e‖ ^ 2 -
      2 * r * inner ℝ u (z - e) := by
    rw [he, norm_sub_sq_real, norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le,
      real_inner_smul_left]
    ring
  nlinarith [norm_nonneg (e + r • u - z)]

lemma ray_norm_sq (e u h z : E) (s : ℝ) (hu : ‖u‖ = 1) :
    ‖e + s • u + h - z‖ ^ 2 = s ^ 2 + 2 * s * inner ℝ u h + ‖h‖ ^ 2 +
      ‖z - e‖ ^ 2 - 2 * s * inner ℝ u (z - e) - 2 * inner ℝ h (z - e) := by
  have he : e + s • u + h - z = s • u + h - (z - e) := by abel
  rw [he, norm_sub_sq_real, norm_add_sq_real, norm_smul, hu, mul_one,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, Real.norm_eq_abs, sq_abs]
  ring

lemma proximal_ray_remainder [ProperSpace E] (F : Set E) (hF : F.Nonempty)
    (hFc : IsClosed F) (e u : E) (he : e ∈ F) (r s : ℝ) (hr : 0 < r)
    (hs : 0 < s) (hsr : 2 * s ≤ r) (hu : ‖u‖ = 1)
    (hp : Metric.infDist (e + r • u) F = r) (h : E) :
    |Metric.infDist (e + s • u + h) F ^ 2 - s ^ 2 - 2 * s * inner ℝ u h| ≤ ‖h‖ ^ 2 := by
  have hupper := Metric.infDist_le_dist_of_mem (x := e + s • u + h) he
  rw [dist_eq_norm] at hupper
  have hnupper := ray_norm_sq e u h e s hu
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), inner_zero_right, mul_zero,
    add_zero, sub_zero] at hnupper
  have hd0 := Metric.infDist_nonneg (x := e + s • u + h) (s := F)
  have hupp : Metric.infDist (e + s • u + h) F ^ 2 ≤
      s ^ 2 + 2 * s * inner ℝ u h + ‖h‖ ^ 2 := by
    nlinarith [norm_nonneg (e + s • u + h - e)]
  obtain ⟨z, hz, hzd⟩ := hFc.exists_infDist_eq_dist hF (e + s • u + h)
  have hprox := proximal_pairing F e u r hr hu hp z hz
  have hhalf : 2 * s * inner ℝ u (z - e) ≤ ‖z - e‖ ^ 2 / 2 := by
    by_cases hi : inner ℝ u (z - e) ≤ 0
    · nlinarith [sq_nonneg ‖z - e‖]
    · have hm := mul_le_mul_of_nonneg_right hsr (le_of_not_ge hi)
      nlinarith
  have hyoung : 2 * inner ℝ h (z - e) ≤ ‖z - e‖ ^ 2 / 2 + 2 * ‖h‖ ^ 2 := by
    have hn := sq_nonneg ‖z - e - (2 : ℝ) • h‖
    rw [norm_sub_sq_real, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      real_inner_smul_right, real_inner_comm h (z - e)] at hn
    nlinarith
  have hnorm := ray_norm_sq e u h z s hu
  rw [dist_eq_norm] at hzd
  have hlow : s ^ 2 + 2 * s * inner ℝ u h - ‖h‖ ^ 2 ≤
      Metric.infDist (e + s • u + h) F ^ 2 := by rw [hzd]; nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma proximal_ray_distance [ProperSpace E] (F : Set E) (hF : F.Nonempty)
    (hFc : IsClosed F) (e u : E) (he : e ∈ F) (r s : ℝ) (hr : 0 < r)
    (hs : 0 < s) (hsr : 2 * s ≤ r) (hu : ‖u‖ = 1)
    (hp : Metric.infDist (e + r • u) F = r) :
    Metric.infDist (e + s • u) F = s := by
  have hh := proximal_ray_remainder F hF hFc e u he r s hr hs hsr hu hp 0
  simp only [add_zero, inner_zero_right, mul_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    abs_nonpos_iff] at hh
  have := Metric.infDist_nonneg (x := e + s • u) (s := F)
  nlinarith

lemma proximal_ray_hasFDerivAt [ProperSpace E] (F : Set E) (hF : F.Nonempty)
    (hFc : IsClosed F) (e u : E) (he : e ∈ F) (r s : ℝ) (hr : 0 < r)
    (hs : 0 < s) (hsr : 2 * s ≤ r) (hu : ‖u‖ = 1)
    (hp : Metric.infDist (e + r • u) F = r) :
    HasFDerivAt (fun y => Metric.infDist y F) (innerSL ℝ u) (e + s • u) := by
  have hd := proximal_ray_distance F hF hFc e u he r s hr hs hsr hu hp
  have hsq : HasFDerivAt (fun y => Metric.infDist y F ^ 2)
      ((2 * s) • innerSL ℝ u) (e + s • u) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    apply Asymptotics.IsBigO.trans_isLittleO _
      (Asymptotics.isLittleO_norm_pow_id (E' := E) (by decide : 1 < 2))
    apply Asymptotics.IsBigO.of_norm_le
    intro h
    simpa only [Real.norm_eq_abs, smul_apply, innerSL_apply_apply,
      smul_eq_mul, hd] using proximal_ray_remainder F hF hFc e u he r s hr hs hsr hu hp h
  have hh := hsq.sqrt (by rw [hd]; positivity)
  have heq : (fun y => Real.sqrt (Metric.infDist y F ^ 2)) = fun y => Metric.infDist y F := by
    funext y
    exact Real.sqrt_sq (Metric.infDist_nonneg)
  rw [heq, hd, Real.sqrt_sq hs.le, smul_smul, one_div_mul_cancel (by positivity : (2 * s) ≠ 0),
    one_smul] at hh
  exact hh

end ClarkeGradients.FlowProof

end

/- Complete checked body: ProximalNormals -/
section

set_option autoImplicit false

open Filter Topology InnerProductSpace RealInnerProductSpace

namespace ClarkeGradients.FlowProof

open ClarkeGradients.FlowInvariance ClarkeGradients.Shared

lemma proximal_unit_gradientLimit {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (hF : F.Nonempty) (hFc : IsClosed F) (e u : EuclideanSpace ℝ (Fin n)) (he : e ∈ F)
    (r : ℝ) (hr : 0 < r) (hu : ‖u‖ = 1)
    (hp : Metric.infDist (e + r • u) F = r) :
    u ∈ gradientLimits (fun y => Metric.infDist y F) e := by
  let s : ℕ → ℝ := fun k => r / ((k + 2 : ℕ) : ℝ)
  have hs (k : ℕ) : 0 < s k := by dsimp [s]; positivity
  have hsr (k : ℕ) : 2 * s k ≤ r := by
    have hd : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
    have htwo : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
    dsimp [s]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  have ht : Tendsto s atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 2)
  have hder (k : ℕ) := proximal_ray_hasFDerivAt F hF hFc e u he r (s k) hr (hs k)
    (hsr k) hu hp
  have hgrad (k : ℕ) : gradient (fun y => Metric.infDist y F) (e + s k • u) = u := by
    exact (show HasGradientAt (fun y => Metric.infDist y F) u (e + s k • u) from hder k).gradient
  refine ⟨fun k => s k • u, ?_, fun k => (hder k).differentiableAt, ?_⟩
  · simpa using ht.smul_const u
  · simpa only [hgrad] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))

lemma proximal_normal_mem {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (hF : F.Nonempty) (hFc : IsClosed F) (y e : EuclideanSpace ℝ (Fin n))
    (he : e ∈ F) (hd : dist y e = Metric.infDist y F) (hne : y ≠ e) :
    ‖y - e‖⁻¹ • (y - e) ∈ normalCone F e := by
  let r := ‖y - e‖
  let u := r⁻¹ • (y - e)
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, ← show ‖y - e‖ = r from rfl,
      inv_mul_cancel₀ hr.ne']
  have hy : e + r • u = y := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hp : Metric.infDist (e + r • u) F = r := by rw [hy, ← hd, dist_eq_norm]
  have hg := proximal_unit_gradientLimit F hF hFc e u he r hr hu hp
  apply subset_closure
  refine ⟨1, by norm_num, ?_⟩
  simpa only [one_smul, generalizedGradient, u, r] using (subset_convexHull ℝ _ hg)

lemma tangent_of_gradientLimits {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (x v : EuclideanSpace ℝ (Fin n))
    (h : ∀ g ∈ gradientLimits (fun y => Metric.infDist y F) x, inner ℝ v g ≤ 0) :
    v ∈ tangentCone F x := by
  have hc : Convex ℝ {g : EuclideanSpace ℝ (Fin n) | inner ℝ v g ≤ 0} := by
    exact convex_halfSpace_le (LinearMap.isLinearMap_of_compatibleSMul ℝ (innerSL ℝ v).toLinearMap) 0
  have hG : generalizedGradient (fun y => Metric.infDist y F) x ⊆
      {g : EuclideanSpace ℝ (Fin n) | inner ℝ v g ≤ 0} :=
    convexHull_min h hc
  have hS : {p : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 < s ∧
      s • p ∈ generalizedGradient (fun y => Metric.infDist y F) x} ⊆
      {g | inner ℝ v g ≤ 0} := by
    rintro p ⟨s, hs, hp⟩
    have hh := hG hp
    change inner ℝ v (s • p) ≤ 0 at hh
    rw [real_inner_smul_right] at hh
    exact nonpos_of_mul_nonpos_right hh hs
  have hclosed : IsClosed {g : EuclideanSpace ℝ (Fin n) | inner ℝ v g ≤ 0} :=
    isClosed_le (innerSL ℝ v).continuous continuous_const
  exact fun p hp => closure_minimal hS hclosed hp

end ClarkeGradients.FlowProof

end

/- Complete checked body: FlowNecessity -/
section

set_option autoImplicit false

open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology
open ClarkeGradients.FlowInvariance ClarkeGradients.Shared

namespace ClarkeGradients.FlowProof

theorem invariant_nearest_velocity {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x))
    (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hInv : FlowInvariant X F)
    {y e w : EuclideanSpace ℝ (Fin n)} (he : e ∈ F)
    (hne : dist y e = infDist y F) (hw : w ∈ X e) :
    inner ℝ (y-e) w ≤ 0 := by
  obtain ⟨x,htraj,hx0,hderiv⟩ := exists_trajectory_initial X hX hLip e w hw
  have hxf : ∀ t ∈ Icc (0:ℝ) 1, x t ∈ F := hInv x htraj (hx0 ▸ he)
  have hmin : IsLocalMinOn (fun t : ℝ => ‖y-x t‖^2) (Icc 0 1) 0 := by
    apply IsMinOn.localize
    intro t ht
    have hdist := infDist_le_dist_of_mem (x := y) (hxf t ht)
    rw [← hne,dist_eq_norm,dist_eq_norm] at hdist
    dsimp only
    rw [hx0]
    exact pow_le_pow_left₀ (norm_nonneg (y-e)) hdist 2
  have hd := (hderiv.const_sub y).norm_sq
  have hcone : (1:ℝ) ∈ posTangentConeAt (Icc 0 1) 0 := by
    have hseg : segment ℝ (0:ℝ) 1 ⊆ Icc 0 1 :=
      (convex_Icc (0:ℝ) 1).segment_subset (by norm_num) (by norm_num)
    have h := sub_mem_posTangentConeAt_of_segment_subset hseg
    simpa only [sub_zero] using h
  have hnonneg := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply_one,hx0,inner_neg_right] at hnonneg
  linarith

theorem invariant_gradient_bound {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x))
    (hLip : IsLipschitzMultifunction X) {K : ℝ} (hK : 0 ≤ K)
    (hbound : HasMultifunctionBound X K)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (hInv : FlowInvariant X F) {x v y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) (hv : v ∈ X x)
    (hdiff : DifferentiableAt ℝ (fun z => infDist z F) y) :
    inner ℝ (gradient (fun z => infDist z F) y) v ≤ 2*K*‖y-x‖ := by
  by_cases hz : gradient (fun z => infDist z F) y = 0
  · rw [hz,inner_zero_left]
    positivity
  obtain ⟨_hy,⟨e,⟨he,hed⟩,_hunique⟩,hgrad⟩ :=
    checked_gradient_infDist_of_ne_zero F hF hFc y hdiff hz
  obtain ⟨w,hw,hd⟩ := hbound x e v hv
  have hn := invariant_nearest_velocity X hX hLip F hInv he hed hw
  have hg : inner ℝ (gradient (fun z => infDist z F) y) w ≤ 0 := by
    rw [hgrad e he hed,inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) hn
  have hedist : ‖x-e‖ ≤ 2*‖y-x‖ := by
    have htri := norm_sub_le_norm_sub_add_norm_sub x y e
    have hnear := infDist_le_dist_of_mem (x := y) hx
    rw [← hed,dist_eq_norm,dist_eq_norm] at hnear
    rw [norm_sub_rev x y] at htri
    linarith
  have hgradnorm := aux_gid_normle F y
  have hin := real_inner_le_norm (gradient (fun z => infDist z F) y) (v-w)
  rw [inner_sub_right] at hin
  have hm : ‖gradient (fun z => infDist z F) y‖*‖v-w‖ ≤ ‖v-w‖ := by
    nlinarith [norm_nonneg (v-w)]
  have hvw : ‖v-w‖ ≤ K*(2*‖y-x‖) :=
    hd.trans (mul_le_mul_of_nonneg_left hedist hK)
  linarith

theorem tangent_of_flow_invariant {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x))
    (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (hInv : FlowInvariant X F) : ∀ x ∈ F, X x ⊆ tangentCone F x := by
  obtain ⟨K,hK⟩ := hLip
  have hb : HasMultifunctionBound X (max K 0) := by
    intro a b v hv
    obtain ⟨w,hw,hd⟩ := hK a b v hv
    exact ⟨w,hw,hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  intro x hx v hv
  apply tangent_of_gradientLimits F x v
  intro ζ hζ
  obtain ⟨d,hd0,hdd,hgrad⟩ := hζ
  have hlim : Tendsto (fun j => inner ℝ (gradient (fun z => infDist z F) (x+d j)) v)
      atTop (𝓝 (inner ℝ ζ v)) := hgrad.inner tendsto_const_nhds
  have hright : Tendsto (fun j => 2*(max K 0)*‖(x+d j)-x‖) atTop (𝓝 0) := by
    simpa only [add_sub_cancel_left,norm_zero,mul_zero] using
      tendsto_const_nhds.mul hd0.norm
  have hi : inner ℝ ζ v ≤ 0 := le_of_tendsto_of_tendsto hlim hright
    (Eventually.of_forall (fun j => invariant_gradient_bound X hX ⟨K,hK⟩
      (le_max_right _ _) hb F hF hFc hInv hx hv (hdd j)))
  simpa only [real_inner_comm] using hi

end ClarkeGradients.FlowProof

end

/- Complete checked body: DistanceGrowth -/
section

set_option autoImplicit false

open Filter Topology MeasureTheory InnerProductSpace RealInnerProductSpace

namespace ClarkeGradients.FlowProof

open ClarkeGradients.FlowInvariance

lemma distance_derivative_le {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) (K : ℝ)
    (hK : ∀ x₁ x₂, ∀ v₁ ∈ X x₁, ∃ v₂ ∈ X x₂, ‖v₁ - v₂‖ ≤ K * ‖x₁ - x₂‖)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (htan : ∀ e ∈ F, X e ⊆ tangentCone F e)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ X (x t)) (hx : HasDerivAt x v t) (d : ℝ)
    (hd : HasDerivAt (fun a => Metric.infDist (x a) F) d t) :
    d ≤ K * Metric.infDist (x t) F := by
  by_cases hzero : Metric.infDist (x t) F = 0
  · have hm : IsLocalMin (fun a => Metric.infDist (x a) F) t :=
      Filter.Eventually.of_forall (fun a => by dsimp only; rw [hzero]; exact Metric.infDist_nonneg)
    rw [hm.hasDerivAt_eq_zero hd, hzero, mul_zero]
  obtain ⟨e, he, heq⟩ := hFc.exists_infDist_eq_dist hF (x t)
  have hnorm : Metric.infDist (x t) F = ‖x t - e‖ := by simpa only [dist_eq_norm] using heq
  have hn : 0 < ‖x t - e‖ := by rw [← hnorm]; exact lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hzero)
  have hxe : x t ≠ e := by intro h; simp [h] at hn
  let p := ‖x t - e‖⁻¹ • (x t - e)
  have hp : p ∈ normalCone F e := proximal_normal_mem F hF hFc (x t) e he heq.symm hxe
  have hpn : ‖p‖ = 1 := by
    dsimp [p]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  obtain ⟨w, hw, hclose⟩ := hK (x t) e v hv
  have hin : inner ℝ p w ≤ 0 := by
    have hh := htan e he hw p hp
    simpa only [real_inner_comm p w] using hh
  have hm : IsLocalMin (fun a => ‖x a - e‖ ^ 2 - Metric.infDist (x a) F ^ 2) t := by
    apply Filter.Eventually.of_forall
    intro a
    dsimp only
    rw [hnorm, sub_self]
    have hu := Metric.infDist_le_dist_of_mem (x := x a) he
    rw [dist_eq_norm] at hu
    nlinarith [Metric.infDist_nonneg (x := x a) (s := F), norm_nonneg (x a - e)]
  have hz := hm.hasDerivAt_eq_zero ((hx.sub_const e).norm_sq.sub (hd.pow 2))
  norm_num [hnorm] at hz
  have hip : inner ℝ p v = d := by
    dsimp [p]
    rw [real_inner_smul_left]
    field_simp [hn.ne']
    nlinarith
  have hcs := real_inner_le_norm p (v - w)
  rw [hpn, one_mul, inner_sub_right] at hcs
  rw [hip] at hcs
  rw [hnorm]
  linarith

lemma distance_ac {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : AbsolutelyContinuousOnInterval x 0 1) :
    AbsolutelyContinuousOnInterval (fun t => Metric.infDist (x t) F) 0 1 := by
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) _ hx
  intro E
  apply Finset.sum_le_sum
  intro i _
  simpa using (Metric.lipschitz_infDist_pt (s := F)).dist_le_mul (x (E.2 i).1) (x (E.2 i).2)

lemma distance_growth_ae {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) (K : ℝ)
    (hK : ∀ x₁ x₂, ∀ v₁ ∈ X x₁, ∃ v₂ ∈ X x₂, ‖v₁ - v₂‖ ≤ K * ‖x₁ - x₂‖)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (htan : ∀ e ∈ F, X e ⊆ tangentCone F e)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : IsTrajectory X x) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      deriv (fun a => Metric.infDist (x a) F) t ≤ K * Metric.infDist (x t) F := by
  have hd := (distance_ac F x hx.1).ae_differentiableAt
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      DifferentiableAt ℝ (fun a => Metric.infDist (x a) F) t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    simpa only [Set.uIcc_of_le zero_le_one] using hd
  filter_upwards [hx.2, hdiff] with t ht hdt
  obtain ⟨v, hv, hvd⟩ := ht
  exact distance_derivative_le X K hK F hF hFc htan x t v hv hvd _ hdt.hasDerivAt

end ClarkeGradients.FlowProof

end

/- Complete checked body: ACGronwall -/
section

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace ClarkeGradients.FlowProof

lemma ac_gronwall_zero (f : ℝ → ℝ) (K : ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hf0 : f 0 = 0)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t)
    (hder : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv f t ≤ K * f t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
  let g : ℝ → ℝ := fun t => Real.exp (-K * t) * f t
  have hE : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-K * t)) :=
    (contDiff_const.mul contDiff_id).exp
  have hg : AbsolutelyContinuousOnInterval g 0 1 :=
    hE.contDiffOn.absolutelyContinuousOnInterval.mul hf
  have hdf : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), DifferentiableAt ℝ f t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    simpa only [Set.uIcc_of_le zero_le_one] using hf.ae_differentiableAt
  have hneg : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv g t ≤ 0 := by
    filter_upwards [hder, hdf] with t ht hdt
    have he := ((hasDerivAt_id t).const_mul (-K)).exp
    have hp := he.mul hdt.hasDerivAt
    change HasDerivAt g _ t at hp
    rw [hp.deriv]
    have hm := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-K * t)).le
    simp only [id_eq, mul_one] at *
    nlinarith
  intro t ht
  have hgT : AbsolutelyContinuousOnInterval g 0 t := hg.mono (by
    simp only [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc le_rfl ht.2)
  have hi : (∫ a in (0 : ℝ)..t, deriv g a) ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    apply integral_nonpos_of_ae
    exact ae_restrict_of_ae_restrict_of_subset
      (show Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 1 from
        fun a ha => ⟨ha.1.le, ha.2.trans ht.2⟩) hneg
  rw [hgT.integral_deriv_eq_sub] at hi
  have hp : Real.exp (-K * t) * f t ≤ 0 := by simpa [g, hf0] using hi
  exact le_antisymm (nonpos_of_mul_nonpos_right hp (Real.exp_pos (-K * t))) (hpos t ht)

end ClarkeGradients.FlowProof

end

/- Complete checked body: FlowSufficiency -/
section

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace ClarkeGradients.FlowProof

open ClarkeGradients.FlowInvariance

theorem flow_invariant_of_tangent {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (htan : ∀ e ∈ F, X e ⊆ tangentCone F e) : FlowInvariant X F := by
  obtain ⟨K, hK⟩ := hLip
  intro x hx hx0 t ht
  have hzero := ac_gronwall_zero (fun a => Metric.infDist (x a) F) K
    (distance_ac F x hx.1) (Metric.infDist_zero_of_mem hx0)
    (fun _ _ => Metric.infDist_nonneg) (distance_growth_ae X K hK F hF hFc htan x hx) t ht
  exact (hFc.mem_iff_infDist_zero hF).mpr hzero

end ClarkeGradients.FlowProof

end

/- Complete checked body: FlowRoot -/
section

set_option autoImplicit false

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Theorem (4.4): let `X` be a Lipschitz multifunction (4.2) whose values `X(x)`
are nonempty and compact (standing assumption of §4), and let `F` be a nonempty closed subset of
`ℝⁿ`. Then `F` is flow-invariant for `X` (4.3) if and only if `X(x) ⊆ T_F(x)` for every `x ∈ F`,
where `T_F(x)` is the Clarke tangent cone (3.6). -/
theorem flowInvariant_iff_subset_tangentCone {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x)) (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F) :
    FlowInvariant X F ↔ ∀ x ∈ F, X x ⊆ tangentCone F x := by
  exact ⟨ClarkeGradients.FlowProof.tangent_of_flow_invariant X hX hLip F hF hFc,
    ClarkeGradients.FlowProof.flow_invariant_of_tangent X hLip F hF hFc⟩

end ClarkeGradients.FlowInvariance

end

open ClarkeGradients.FlowInvariance


theorem solution {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x)) (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F) :
    FlowInvariant X F ↔ ∀ x ∈ F, X x ⊆ tangentCone F x := by
  exact ClarkeGradients.FlowInvariance.flowInvariant_iff_subset_tangentCone X hX hLip F hF hFc

#print axioms ClarkeGradients.FlowInvariance.flowInvariant_iff_subset_tangentCone
#print axioms solution
