-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.remark_7_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:41:19.327692+00:00
-- url     : https://prove2.me/submissions/84c28c36-06fa-473d-8d1f-f3a4a58ee0da

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Alg76
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_2
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_3
import Theorems.Thm_GenNewtonSubgrad_ProxReg_scalarization_2_11

open Filter Topology
open scoped InnerProductSpace

namespace GNCAux
open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma quadF_expand (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x h : E) :
    quadF A b α (x + h) = quadF A b α x + ⟪A x + b, h⟫_ℝ + (1/2) * ⟪A h, h⟫_ℝ := by
  have hs : ⟪A h, x⟫_ℝ = ⟪h, A x⟫_ℝ := by
    have := hA.isSymmetric h x
    simpa using this
  simp only [quadF, map_add, inner_add_left, inner_add_right]
  rw [hs, real_inner_comm h (A x)]
  ring

lemma hasGradientAt_quadF (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x : E) :
    HasGradientAt (quadF A b α) (A x + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have key : ∀ h : E, quadF A b α (x + h) - quadF A b α x - (InnerProductSpace.toDual ℝ E (A x + b)) h
      = (1/2) * ⟪A h, h⟫_ℝ := by
    intro h
    rw [quadF_expand A hA b α x h, InnerProductSpace.toDual_apply_apply]
    ring
  simp_rw [key]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : E => ‖h‖ ^ 2) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound (‖A‖ / 2) (Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_pow, norm_norm]
    have h1 : |⟪A h, h⟫_ℝ| ≤ ‖A‖ * ‖h‖ ^ 2 := by
      calc |⟪A h, h⟫_ℝ| ≤ ‖A h‖ * ‖h‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖h‖ * ‖h‖ := by gcongr; exact A.le_opNorm h
        _ = ‖A‖ * ‖h‖ ^ 2 := by ring
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    nlinarith
  · exact Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2)

lemma gradient_quadF (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x : E) :
    gradient (quadF A b α) x = A x + b :=
  (hasGradientAt_quadF A hA b α x).gradient

lemma contDiff_quadF (A : E →L[ℝ] E) (b : E) (α : ℝ) : ContDiff ℝ 2 (quadF A b α) := by
  unfold quadF
  have h1 : ContDiff ℝ 2 (fun x : E => ⟪A x, x⟫_ℝ) := (A.contDiff).inner ℝ contDiff_id
  have h2 : ContDiff ℝ 2 (fun x : E => ⟪b, x⟫_ℝ) := contDiff_const.inner ℝ contDiff_id
  exact ((contDiff_const.mul h1).add h2).add contDiff_const


end GNCAux

open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNCAux in
theorem solution {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      ∃ U ∈ 𝓝 xbar, ∀ x ∈ U,
        (fbe (quadF A b α) g γ x ≠ ⊤ ∧ fbe (quadF A b α) g γ x ≠ ⊥ ∧
          DifferentiableAt ℝ (fun y => (fbe (quadF A b α) g γ y).toReal) x) ∧
        (∃ p : EuclideanSpace ℝ (Fin n),
          GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) = {p}) ∧
        (0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) x ↔
          gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x = 0) ∧
        (∀ x' : EuclideanSpace ℝ (Fin n), alg76Step A b α g γ x x' ↔
          GenNewtonSubgrad.ProxReg.alg53Step
            (fun y => (fbe (quadF A b α) g γ y).toReal) x x') ∧
        ∀ v ∈ GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)),
        gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x = γ⁻¹ • shiftOp A γ (x - v) ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          -(γ⁻¹ • (x - v)) - A d ∈
              GenNewtonSubgrad.ProxReg.secondSubdiff g v (γ⁻¹ • ((x - γ • (A x + b)) - v)) (x - v + d) ↔
            -gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x ∈
              GenNewtonSubgrad.ProxReg.coderiv (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) x
                (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x) d) ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          -gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x ∈
              GenNewtonSubgrad.ProxReg.coderiv (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) x
                (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x) d ↔
            -gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x ∈
              NonconvexSplitting.Shared.LimitingSubdiff
                (fun z => ((⟪d, gradient (fun y => (fbe (quadF A b α) g γ y).toReal) z⟫_ℝ : ℝ) :
                  EReal)) x) := by
  classical
  have hgrad : ∀ x, gradient (quadF A b α) x = A x + b := gradient_quadF A hA b α
  have hfd : ∀ x, fderiv ℝ (gradient (quadF A b α)) x = A := by
    intro x
    have : gradient (quadF A b α) = fun y => A y + b := funext hgrad
    rw [this]; exact (A.hasFDerivAt.add_const b).fderiv
  obtain ⟨γ2, hγ2, hγ2r, h72⟩ := proposition_7_2 (quadF A b α) g xbar r ε
    ⟨Set.univ, Filter.univ_mem, (contDiff_quadF A b α).contDiffOn⟩ hstat hg hpb
    (by rw [hgrad]; exact hpr)
  obtain ⟨γ3, hγ3, -, h73⟩ := proposition_7_3 A hA b α g xbar r ε hg hpb hpr hstat
  refine ⟨min γ2 γ3, lt_min hγ2 hγ3, (min_le_left _ _).trans hγ2r, fun γ hγ hlt hB => ?_⟩
  have lt2 : γ < γ2 := lt_of_lt_of_le hlt (min_le_left _ _)
  have lt3 : γ < γ3 := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨U2, hU2, P, hP, ⟨L, hL⟩, -, -, -, hform, h75⟩ := h72 γ hγ lt2
  obtain ⟨U3, hU3, h3⟩ := h73 γ hγ lt3 hB
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (fbe (quadF A b α) g γ y).toReal with hψdef
  have hP' : ∀ x ∈ U2, GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) = {P x} := by
    intro x hx; have := hP x hx; rwa [hgrad] at this
  have hPmem : ∀ x ∈ U2, P x ∈ GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) := by
    intro x hx; rw [hP' x hx]; exact Set.mem_singleton _
  have hsh : ∀ y, shiftOp A γ y = y - γ • A y := by intro y; simp [shiftOp]
  have hgψ : ∀ x ∈ U2, gradient ψ x = γ⁻¹ • shiftOp A γ (x - P x) := by
    intro x hx
    rw [hform x hx, hfd, hsh]
  have hFL : LipschitzOnWith (‖γ⁻¹ • shiftOp A γ‖₊ * (1 + L))
      (fun x => (γ⁻¹ • shiftOp A γ) (x - P x)) U2 :=
    (γ⁻¹ • shiftOp A γ).lipschitz.comp_lipschitzOnWith
      ((LipschitzWith.id.lipschitzOnWith).sub hL)
  have hgL : LipschitzOnWith (‖γ⁻¹ • shiftOp A γ‖₊ * (1 + L)) (gradient ψ) U2 := by
    intro x hx y hy
    rw [hgψ x hx, hgψ y hy]; exact hFL hx hy
  refine ⟨interior (U2 ∩ U3), interior_mem_nhds.2 (Filter.inter_mem hU2 hU3), fun x hx => ?_⟩
  have hxU := interior_subset hx
  have hx2 : x ∈ U2 := hxU.1
  have hx3 : x ∈ U3 := hxU.2
  have hstop : 0 ∈ LimitingSubdiff (sumFn (quadF A b α) g) x ↔ gradient ψ x = 0 :=
    (h75 x hx2 (by rw [hfd]; exact hB)).symm
  have hscal : ∀ d, -gradient ψ x ∈ coderiv (sv (gradient ψ)) x (gradient ψ x) d ↔
      -gradient ψ x ∈ LimitingSubdiff (fun z => ((⟪d, gradient ψ z⟫_ℝ : ℝ) : EReal)) x := by
    intro d
    rw [scalarization_2_11 (gradient ψ) x
      ⟨interior (U2 ∩ U3), isOpen_interior.mem_nhds hx, _,
        hgL.mono (interior_subset.trans Set.inter_subset_left)⟩ d]
  have hv : ∀ v ∈ GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)),
      gradient ψ x = γ⁻¹ • shiftOp A γ (x - v) ∧
      ∀ d, (-(γ⁻¹ • (x - v)) - A d ∈ secondSubdiff g v (γ⁻¹ • ((x - γ • (A x + b)) - v)) (x - v + d) ↔
        -gradient ψ x ∈ coderiv (sv (gradient ψ)) x (gradient ψ x) d) := by
    intro v hv'
    have hvP : v = P x := by rw [hP' x hx2] at hv'; exact hv'
    subst hvP
    refine ⟨hgψ x hx2, fun d => ?_⟩
    obtain ⟨-, p, hp, hcd⟩ := h3 x hx3
    have hpv : p = P x := by
      rw [hP' x hx2] at hp; exact (Set.singleton_eq_singleton_iff.1 hp).symm
    rw [hcd]
    have hinv : shiftInv A γ (-gradient ψ x) = -(γ⁻¹ • (x - P x)) := by
      rw [hgψ x hx2]
      have : -(γ⁻¹ • shiftOp A γ (x - P x)) = shiftOp A γ (-(γ⁻¹ • (x - P x))) := by
        rw [map_neg, map_smul]
      rw [this]
      exact Function.leftInverse_invFun hB.1 _
    have e : d - γ • -(γ⁻¹ • (x - P x)) = x - P x + d := by
      rw [smul_neg, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]; abel
    rw [hinv, hpv, e]
  refine ⟨(h3 x hx3).1, (h3 x hx3).2.imp fun p hp => hp.1, hstop, fun x' => ?_,
    fun v hv' => ⟨(hv v hv').1, (hv v hv').2, hscal⟩⟩
  unfold alg76Step alg53Step
  constructor
  · rintro (⟨h0, rfl⟩ | ⟨h0, v, hv', h718⟩)
    · exact Or.inl ⟨hstop.1 h0, rfl⟩
    · exact Or.inr ⟨fun h => h0 (hstop.2 h), (hscal (x' - x)).1 (((hv v hv').2 (x' - x)).1 h718)⟩
  · rintro (⟨h0, rfl⟩ | ⟨h0, hin⟩)
    · exact Or.inl ⟨hstop.2 h0, rfl⟩
    · exact Or.inr ⟨fun h => h0 (hstop.1 h), P x, hPmem x hx2,
        ((hv _ (hPmem x hx2)).2 (x' - x)).2 ((hscal _).2 hin)⟩
