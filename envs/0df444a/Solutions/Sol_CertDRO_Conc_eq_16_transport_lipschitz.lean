-- Prove2me | solution 1 for CertDRO.Conc.eq_16_transport_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T14:45:31.072991+00:00
-- url     : https://prove2.me/submissions/8dba1587-701d-4062-9978-96f6c1bec4d3

import Definitions.Def_CertDRO_Conc_model
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
open Set
namespace TransportStability

lemma paired_optimality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (Z : Set E) (hZ : Convex ℝ Z) (f g c : E → ℝ)
    (x y gx gy : E) (hx : x ∈ Z) (hy : y ∈ Z) (γ : ℝ) (hγ : 0 ≤ γ)
    (hc : StrongConvexOn Z 1 c) (hfx : HasGradientAt f gx x) (hgy : HasGradientAt g gy y)
    (hmaxx : ∀ z ∈ Z, f z - γ*c z ≤ f x - γ*c x)
    (hmaxy : ∀ z ∈ Z, g z - γ*c z ≤ g y - γ*c y) :
    γ*‖y-x‖^2 ≤ ⟪gy-gx,y-x⟫_ℝ := by
  let u : ℝ → E := fun t => (1-t) • x + t • y
  let v : ℝ → E := fun t => (1-t) • y + t • x
  let F : ℝ → ℝ := fun t => f (u t) + g (v t) + γ*t*(1-t)*‖y-x‖^2
  have hm : IsMaxOn F (Icc 0 1) 0 := by
    intro t ht
    have hu : u t ∈ Z := hZ hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hv : v t ∈ Z := hZ hy hx (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hc1 := hc.2 hx hy (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
    have hc2 := hc.2 hy hx (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
    have hcc : c (u t) + c (v t) ≤ c x + c y - t*(1-t)*‖y-x‖^2 := by
      dsimp only [u,v]
      simp only [smul_eq_mul,norm_sub_rev x y] at hc1 hc2
      nlinarith
    have hp := mul_le_mul_of_nonneg_left hcc hγ
    have h1 := hmaxx (u t) hu
    have h2 := hmaxy (v t) hv
    have hF0 : F 0 = f x + g y := by simp [F,u,v]
    rw [hF0]
    change f (u t) + g (v t) + γ*t*(1-t)*‖y-x‖^2 ≤ f x + g y
    nlinarith only [h1,h2,hp]
  have hu : HasDerivAt u (y-x) 0 := by
    convert (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0)).smul_const x).add
        ((hasDerivAt_id 0).smul_const y) using 1 <;> simp [u,sub_eq_add_neg,add_comm]
    rfl
  have hv : HasDerivAt v (x-y) 0 := by
    convert (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0)).smul_const y).add
        ((hasDerivAt_id 0).smul_const x) using 1 <;> simp [v,sub_eq_add_neg,add_comm]
    rfl
  have hf : HasDerivAt (fun t => f (u t)) ⟪gx,y-x⟫_ℝ 0 := by
    simpa [Function.comp_def,InnerProductSpace.toDual_apply_apply] using
      hfx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hu (by simp [u])
  have hg : HasDerivAt (fun t => g (v t)) ⟪gy,x-y⟫_ℝ 0 := by
    simpa [Function.comp_def,InnerProductSpace.toDual_apply_apply] using
      hgy.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by simp [v])
  have hp : HasDerivAt (fun t : ℝ => γ*t*(1-t)*‖y-x‖^2) (γ*‖y-x‖^2) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul γ).mul
      ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0))).mul_const (‖y-x‖^2)
  have hd := (hf.add hg).add hp
  have ht : (1:ℝ) ∈ posTangentConeAt (Icc (0:ℝ) 1) 0 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset
      (show segment ℝ (0:ℝ) 1 ⊆ Icc 0 1 by rw [segment_eq_Icc zero_le_one])
  have hle := hm.localize.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt ht
  have hle : ⟪gx,y-x⟫_ℝ + ⟪gy,x-y⟫_ℝ + γ*‖y-x‖^2 ≤ 0 := by
    simpa using hle
  rw [show x-y = -(y-x) by abel,inner_neg_right] at hle
  simp only [inner_sub_left]
  linarith

end TransportStability
#print axioms TransportStability.paired_optimality

open CertDRO.Conc
theorem solution {d m : ℕ} (Z : Set (CertDRO.SGD.Data m)) (hZ : Convex ℝ Z)
    (Θ : Set (CertDRO.SGD.Param d))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d)
    (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hA : CertDRO.SGD.AssumptionA Z c) (hB : AssumptionB Θ Z ℓ gθ gz Lθθ Lzz Lθz Lzθ)
    (hγ : Lzz < γ) (hT : IsTransportMap Θ Z ℓ c γ T) :
    ∀ z ∈ Z, ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ‖T θ₁ z - T θ₂ z‖ ≤ Lzθ / (γ - Lzz) * ‖θ₁ - θ₂‖  := by
  intro z hz θ₁ hθ₁ θ₂ hθ₂
  let x := T θ₁ z
  let y := T θ₂ z
  have hx : x ∈ Z := (hT θ₁ hθ₁ z hz).1
  have hy : y ∈ Z := (hT θ₂ hθ₂ z hz).1
  have hγ0 : 0 ≤ γ := le_trans hB.nonneg.2.1 hγ.le
  have hp := TransportStability.paired_optimality Z hZ (ℓ θ₁) (ℓ θ₂)
    (fun w => c w z) x y (gz θ₁ x) (gz θ₂ y) hx hy γ hγ0 (hA.strongConvexOn z hz)
    (hB.hasGradient_z θ₁ hθ₁ x hx) (hB.hasGradient_z θ₂ hθ₂ y hy)
    (hT θ₁ hθ₁ z hz).2 (hT θ₂ hθ₂ z hz).2
  have hn : ‖gz θ₂ y - gz θ₁ x‖ ≤ Lzθ*‖θ₁-θ₂‖ + Lzz*‖y-x‖ := by
    calc
      _ ≤ ‖gz θ₂ y - gz θ₁ y‖ + ‖gz θ₁ y - gz θ₁ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add
        (by simpa only [norm_sub_rev θ₂ θ₁] using hB.lip_zθ θ₂ hθ₂ θ₁ hθ₁ y hy)
        (hB.lip_zz θ₁ hθ₁ y hy x hx)
  have hi := (real_inner_le_norm (gz θ₂ y-gz θ₁ x) (y-x)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  change ‖x-y‖ ≤ _
  rw [norm_sub_rev x y]
  have hden : 0 < γ-Lzz := sub_pos.mpr hγ
  by_cases he : ‖y-x‖=0
  · rw [he]
    exact mul_nonneg (div_nonneg hB.nonneg.2.2.2 hden.le) (norm_nonneg _)
  · have hd : 0 < ‖y-x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    have hlin : (γ-Lzz)*‖y-x‖ ≤ Lzθ*‖θ₁-θ₂‖ := by
      apply (mul_le_mul_iff_left₀ hd).mp
      nlinarith only [hp,hi]
    calc
      ‖y-x‖ ≤ (Lzθ*‖θ₁-θ₂‖)/(γ-Lzz) := (le_div_iff₀ hden).mpr (by nlinarith only [hlin])
      _ = _ := by ring
#print axioms solution
