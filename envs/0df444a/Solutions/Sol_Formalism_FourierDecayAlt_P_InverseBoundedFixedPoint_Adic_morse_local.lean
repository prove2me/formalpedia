-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.morse_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:28.152369+00:00
-- url     : https://prove2.me/submissions/c4e9eef0-5aa9-420d-9dd9-ef5f520d9bc8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_unit_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MemM_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_int_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrtM
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrt_lip
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sqrt_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MW_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MW_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HH_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HA_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_conj_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_MW
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_inverse_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HA_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (h2 : IsUnit (2 : K)) (m : ℕ) (c z : Kˣ)
    (hcv : (c : K) = 4 * ((m + 1 : ℕ) : K) * (ϖ : K)) (B : Submodule R K)
    (hBc : IsClosed (B : Set K)) (hBz : ∀ b ∈ B, ∃ r ∈ R, b = (z : K) * (c : K) * r) :
    ∃ φ : (Fin m → K) → (Fin m → K),
      Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
      (∀ Λ : Submodule R K, ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
        ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
      ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
        (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
        g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
          ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)) := by
  have := h.t2
  have i0 : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := by simp
  have ic : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by simp
  obtain ⟨a, ha⟩ : ∃ a : K, a = (z : K) * (c : K) := ⟨_, rfl⟩
  obtain ⟨ai, hai⟩ : ∃ ai : K, ai = ((z⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have haai : a * ai = 1 := by
    rw [ha, hai]; linear_combination (c : K) * ((c⁻¹ : Kˣ) : K) * i0 + ic
  have hcancel : ∀ x : K, a * (ai * x) = x := fun x => by linear_combination x * haai
  have hcancel' : ∀ x : K, ai * (a * x) = x := fun x => by linear_combination x * haai
  have hc : ∀ r ∈ R, ∃ u ∈ R, (1 + (c : K) * r) * u = 1 := fun r hr =>
    h.unit_one _ ⟨4 * ((m + 1 : ℕ) : K) * r,
      R.mul_mem (R.mul_mem (ofNat_mem R 4) (natCast_mem R _)) hr, by rw [hcv]; ring⟩
  have hBR : ∀ x ∈ cm a B, x ∈ R := by
    intro x hx
    obtain ⟨r, hr, e⟩ := hBz _ hx
    rw [← ha] at e
    have : x = r := by linear_combination ai * e - (x - r) * haai
    rwa [this]
  have hBcl : IsClosed ((cm a B : Submodule R K) : Set K) := by
    show IsClosed ((fun v => a * v) ⁻¹' (B : Set K))
    exact hBc.preimage (continuous_const.mul continuous_id)
  obtain ⟨Nv, hNv⟩ : ∃ Nv : (Fin m → K) → Matrix (Fin m) (Fin m) K,
      ∀ v, Nv v = ((c⁻¹ : Kˣ) : K) • (MW (wv (c : K) v) - HH K m) := ⟨_, fun _ => rfl⟩
  have hNL : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ R) → (∀ k, v' k ∈ R) →
      (∀ k, v k - v' k ∈ Λ) → MemM Λ (Nv v - Nv v') := by
    intro Λ v v' hv hv' hd i j
    obtain ⟨l, hl, e⟩ := (LW.MW hc i j).2 Λ v v' hv hv' hd
    have : (Nv v - Nv v') i j = l := by
      simp only [hNv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination ((c⁻¹ : Kˣ) : K) * e + l * ic
    rw [this]; exact hl
  have hN0 : Nv 0 = 0 := by
    have : wv (c : K) (0 : Fin m → K) = fun _ => 1 := by
      funext k; simp [wv]
    rw [hNv, this, MW_one, sub_self, smul_zero]
  have hNR : ∀ v : Fin m → K, (∀ k, v k ∈ R) → ∀ i j, Nv v i j ∈ R := by
    intro v hv i j
    have := hNL (Rs R) v 0 hv (fun _ => R.zero_mem) (fun k => by
      show v k - (0 : Fin m → K) k ∈ R
      simpa using hv k) i j
    rw [hN0, sub_zero] at this
    exact this
  have hNs : ∀ v, (Nv v)ᵀ = Nv v := fun v => by
    rw [hNv, Matrix.transpose_smul, Matrix.transpose_sub, MW_symm, HH_symm]
  have hHA := HA_int R m
  have hex : ∀ v : Fin m → K, ∃ Y : Matrix (Fin m) (Fin m) K, (∀ k, v k ∈ R) →
      (∀ i j, Y i j ∈ R) ∧ Y = Nv v - (ϖ : K) • (Y * HA K m * Y) := by
    intro v
    by_cases hv : ∀ k, v k ∈ R
    · obtain ⟨Y, h1, h2⟩ := h.sqrtM (HA K m) (Nv v) hHA (hNR v hv)
      exact ⟨Y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose Y0 hY0 using hex
  have h2R : (2 : K) ∈ R := ofNat_mem R 2
  obtain ⟨hmap, hsurj, hiff⟩ := h.core (cm a B) hBR hBcl (fun v => (2 : K) • (HA K m * Y0 v))
    (fun v hv i j => R.mul_mem h2R (int_mul hHA (hY0 v fun k => hBR _ (hv k)).1 i j))
    (fun Λ v v' hv hv' hd i j => by
      have hvR := fun k => hBR _ (hv k)
      have hvR' := fun k => hBR _ (hv' k)
      have h1 := h.sqrt_lip hHA (hY0 v hvR).1 (hY0 v' hvR').1 (hY0 v hvR).2 (hY0 v' hvR').2 Λ
        (hNL Λ v v' hvR hvR' hd)
      have e : ((2 : K) • (HA K m * Y0 v) - (2 : K) • (HA K m * Y0 v')) i j =
          2 * (HA K m * (Y0 v - Y0 v')) i j := by
        rw [Matrix.mul_sub]
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact mul_mem_sub Λ h2R (h1.mul_left hHA i j))
  obtain ⟨θ, hθ⟩ : ∃ θ : (Fin m → K) → (Fin m → K),
      ∀ v, θ v = v + (ϖ : K) • (((2 : K) • (HA K m * Y0 v)) *ᵥ v) := ⟨_, fun _ => rfl⟩
  simp only [← hθ] at hmap hsurj hiff
  have hquad : ∀ v : Fin m → K, (∀ k, v k ∈ cm a B) →
      θ v ⬝ᵥ (HH K m *ᵥ θ v) = v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v) := by
    intro v hv
    have hvR := fun k => hBR _ (hv k)
    have e1 : θ v = (1 + (2 * (ϖ : K)) • (HA K m * Y0 v)) *ᵥ v := by
      rw [hθ, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_smul,
        mul_comm]
    rw [e1, quad_conj, conj_identity (ϖ : K) (Y0 v) (Nv v)
      (h.sqrt_symm hHA (hY0 v hvR).1 (hY0 v hvR).2 HA_symm (hNs v)) (hY0 v hvR).2, ← hcv, hNv,
      smul_smul, ic, one_smul, add_sub_cancel]
  have hexg : ∀ η : Fin m → K, ∃ v : Fin m → K, (∀ k, η k ∈ cm a B) →
      (∀ k, v k ∈ cm a B) ∧ θ v = η := by
    intro η
    by_cases hη : ∀ k, η k ∈ cm a B
    · obtain ⟨v, h1, h2⟩ := hsurj η hη
      exact ⟨v, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hη⟩
  choose g hg using hexg
  have hsc : ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) → ∀ k, ai * ξ k ∈ cm a B := by
    intro ξ hξ k
    show a * (ai * ξ k) ∈ B
    rw [hcancel]; exact hξ k
  have hIff : ∀ Λ : Submodule R K, ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
      ((∀ k, a * g (fun k => ai * ξ k) k - a * g (fun k => ai * η k) k ∈ Λ) ↔
        ∀ k, ξ k - η k ∈ Λ) := by
    intro Λ ξ η hξ hη
    obtain ⟨hv, e⟩ := hg _ (hsc ξ hξ)
    obtain ⟨hv', e'⟩ := hg _ (hsc η hη)
    have h1 := hiff (cm a Λ) _ _ hv hv'
    rw [e, e'] at h1
    constructor
    · intro hd k
      have := h1.2 (fun k => by
        show a * (_ - _) ∈ Λ
        rw [mul_sub]; exact hd k) k
      have this' : a * (ai * ξ k - ai * η k) ∈ Λ := this
      rwa [mul_sub, hcancel, hcancel] at this'
    · intro hd k
      have := h1.1 (fun k => by
        show a * (ai * ξ k - ai * η k) ∈ Λ
        rw [mul_sub, hcancel, hcancel]; exact hd k) k
      have this' : a * (g (fun k => ai * ξ k) k - g (fun k => ai * η k) k) ∈ Λ := this
      rwa [mul_sub] at this'
  refine ⟨fun ξ k => a * g (fun k => ai * ξ k) k, ⟨?_, ?_, ?_⟩, hIff, ?_⟩
  · intro ξ hξ k
    exact (hg _ (hsc ξ hξ)).1 k
  · intro ξ hξ η hη e
    have := (hIff ⊥ ξ η hξ hη).1 (fun k => by
      have := congrFun e k
      simp only at this
      rw [this, sub_self]; exact Submodule.zero_mem _)
    funext k
    exact sub_eq_zero.1 ((Submodule.mem_bot R).1 (this k))
  · intro b hb
    have hv := hsc b hb
    have hη := hmap _ hv
    refine ⟨fun k => a * θ (fun k => ai * b k) k, fun k => hη k, ?_⟩
    have e1 : (fun k => ai * (a * θ (fun k => ai * b k) k)) = θ (fun k => ai * b k) := by
      funext k; rw [hcancel']
    obtain ⟨hv', e'⟩ := hg _ hη
    have h1 := (hiff ⊥ _ _ hv' hv).1 (fun k => by rw [e', sub_self]; exact Submodule.zero_mem _)
    funext k
    simp only [e1]
    have h3 := sub_eq_zero.1 ((Submodule.mem_bot R).1 (h1 k))
    rw [h3, hcancel]
  · intro ξ hξ
    obtain ⟨hv, e⟩ := hg _ (hsc ξ hξ)
    obtain ⟨v, hvdef⟩ : ∃ v, v = g (fun k => ai * ξ k) := ⟨_, rfl⟩
    rw [← hvdef] at hv e
    simp only [← hvdef]
    have hw : ∀ k, (1 + (c : K) * v k) * wv (c : K) v k = 1 := fun k =>
      (wv_spec hc v k (hBR _ (hv k))).1
    have hφ : ∀ k, (z : K) + a * v k = (z : K) * (1 + (c : K) * v k) := fun k => by rw [ha]; ring
    refine ⟨fun k => ?_, ?_⟩
    · rw [hφ]; exact z.isUnit.mul (IsUnit.of_mul_eq_one _ (hw k))
    · simp only [g0, hφ]
      obtain ⟨W, hW⟩ : ∃ W, W = ∏ k, wv (c : K) v k := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S, S = ∑ k, (c : K) * v k := ⟨_, rfl⟩
      have i1 : (z : K) ^ m * (((z⁻¹ : Kˣ) : K)) ^ m = 1 := by rw [← mul_pow, i0, one_pow]
      have e2 : Ring.inverse (∏ k, (z : K) * (1 + (c : K) * v k)) = (((z⁻¹ : Kˣ) : K)) ^ m * W :=
        inverse_eq (by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hW]
          have hp : (∏ k, (1 + (c : K) * v k)) * ∏ k, wv (c : K) v k = 1 := by
            rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => hw k
          linear_combination ((∏ k, (1 + (c : K) * v k)) * ∏ k, wv (c : K) v k) * i1 + hp)
      have e3 : ∑ k, (z : K) * (1 + (c : K) * v k) = (m : K) * (z : K) + (z : K) * S := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hS]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
      have hq1 := quad_identity (fun k => (c : K) * v k) (wv (c : K) v) hw
      rw [← hW, ← hS] at hq1
      have hq2 : (fun k => (c : K) * v k) ⬝ᵥ (MW (wv (c : K) v) *ᵥ fun k => (c : K) * v k) =
          (c : K) ^ 2 * (v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v)) := by
        have : (fun k => (c : K) * v k) = (c : K) • v := rfl
        rw [this, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      have hq3 : ξ ⬝ᵥ (hessM m z *ᵥ ξ) =
          ((z⁻¹ : Kˣ) : K) * a ^ 2 * (θ v ⬝ᵥ (HH K m *ᵥ θ v)) := by
        have e4 : ξ = a • θ v := by
          funext k
          rw [e]
          show ξ k = a * (ai * ξ k)
          rw [hcancel]
        have e5 : hessM m z = ((z⁻¹ : Kˣ) : K) • HH K m := rfl
        conv_lhs => rw [e4, e5]
        rw [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
          smul_eq_mul, smul_eq_mul, smul_eq_mul]
        ring
      have i2 : Ring.inverse (2 : K) * 2 = 1 := Ring.inverse_mul_cancel _ h2
      rw [e2, e3, hq3, hquad v hv, ha]
      rw [hq2] at hq1
      push_cast
      linear_combination (z : K) * W * i1 -
        Ring.inverse (2 : K) * (z : K) * (c : K) ^ 2 * (v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v)) * i0 -
        Ring.inverse (2 : K) * (z : K) * hq1 - (z : K) * (S + W - 1) * i2
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
