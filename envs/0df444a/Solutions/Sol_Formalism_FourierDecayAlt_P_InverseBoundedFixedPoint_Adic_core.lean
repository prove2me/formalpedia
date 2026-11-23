-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.652148+00:00
-- url     : https://prove2.me/submissions/c48c5c62-3d3b-4bf4-b785-e1b62f21d9ee

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_fp
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_nak

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
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (𝔅 : Submodule R K) (hBR : ∀ x ∈ 𝔅, x ∈ R)
    (hBc : IsClosed (𝔅 : Set K)) (Y : (Fin m → K) → Matrix (Fin m) (Fin m) K)
    (hYR : ∀ v, (∀ k, v k ∈ 𝔅) → ∀ i j, Y v i j ∈ R)
    (hYL : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      (∀ k, v k - v' k ∈ Λ) → MemM Λ (Y v - Y v')) :
    (∀ v, (∀ k, v k ∈ 𝔅) → ∀ k, (v + (ϖ : K) • (Y v *ᵥ v)) k ∈ 𝔅) ∧
    (∀ η : Fin m → K, (∀ k, η k ∈ 𝔅) → ∃ v, (∀ k, v k ∈ 𝔅) ∧ v + (ϖ : K) • (Y v *ᵥ v) = η) ∧
    ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      ((∀ k, (v + (ϖ : K) • (Y v *ᵥ v)) k - (v' + (ϖ : K) • (Y v' *ᵥ v')) k ∈ Λ) ↔
        ∀ k, v k - v' k ∈ Λ) := by
  have := h.t2
  have hmv : ∀ v, (∀ k, v k ∈ 𝔅) → ∀ k, (Y v *ᵥ v) k ∈ 𝔅 := fun v hv k => by
    simp only [Matrix.mulVec, dotProduct]
    exact 𝔅.sum_mem fun j _ => mul_mem_sub 𝔅 (hYR v hv k j) (hv j)
  have key : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      (∀ k, v k - v' k ∈ Λ) → ∀ k, (Y v *ᵥ v) k - (Y v' *ᵥ v') k ∈ Λ := by
    intro Λ v v' hv hv' hd k
    have e : (Y v *ᵥ v) k - (Y v' *ᵥ v') k =
        ∑ j, (Y v k j * (v j - v' j) + v' j * (Y v - Y v') k j) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Λ.sum_mem fun j _ => Λ.add_mem (mul_mem_sub Λ (hYR v hv k j) (hd j))
      (mul_mem_sub Λ (hBR _ (hv' j)) (hYL Λ v v' hv hv' hd k j))
  refine ⟨fun v hv k => 𝔅.add_mem (hv k) (mul_mem_sub 𝔅 h.mem (hmv v hv k)), ?_, ?_⟩
  · intro η hη
    have hXe : {v : Fin m → K | ∀ k, v k ∈ 𝔅} = Set.pi Set.univ fun _ : Fin m => (𝔅 : Set K) := by
      ext v; simp [Set.mem_pi]
    have hBcomp : IsCompact (𝔅 : Set K) := h.isCompact.of_isClosed_subset hBc hBR
    have hXc : IsCompact {v : Fin m → K | ∀ k, v k ∈ 𝔅} := by
      rw [hXe]; exact isCompact_univ_pi fun _ => hBcomp
    obtain ⟨v, hv, e⟩ := h.fp (E := Fin m → K) (ι := Fin m) (fun k v => v k)
      (fun k => continuous_apply k) (fun x y hxy => funext hxy) {v | ∀ k, v k ∈ 𝔅} hXc hXc.isClosed
      ⟨0, fun k => 𝔅.zero_mem⟩ (fun x hx k => hBR _ (hx k))
      (fun v => η - (ϖ : K) • (Y v *ᵥ v))
      (fun v hv k => 𝔅.sub_mem (hη k) (mul_mem_sub 𝔅 h.mem (hmv v hv k)))
      (fun n v hv v' hv' hd k => by
        obtain ⟨l, hl, e⟩ := key (sm ((ϖ : K) ^ n) (Rs R)) v v' hv hv' hd k
        refine ⟨-l, R.neg_mem hl, ?_⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(ϖ : K)) * e)
    refine ⟨v, hv, ?_⟩
    have e2 : η - (ϖ : K) • (Y v *ᵥ v) = v := e
    exact (sub_eq_iff_eq_add.1 e2).symm
  · intro Λ v v' hv hv'
    constructor
    · intro hd
      refine h.nak (fun k => v k - v' k) Λ fun Λ' hd' k => ?_
      refine ⟨_, hd k, _, Λ'.neg_mem (key Λ' v v' hv hv' hd' k), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro hd k
      have e : (v + (ϖ : K) • (Y v *ᵥ v)) k - (v' + (ϖ : K) • (Y v' *ᵥ v')) k =
          (v k - v' k) + (ϖ : K) * ((Y v *ᵥ v) k - (Y v' *ᵥ v') k) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact Λ.add_mem (hd k) (mul_mem_sub Λ h.mem (key Λ v v' hv hv' hd k))
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
