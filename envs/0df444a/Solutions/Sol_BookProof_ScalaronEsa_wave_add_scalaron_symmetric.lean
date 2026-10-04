-- Prove2me | solution 1 for BookProof.ScalaronEsa.wave_add_scalaron_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:15:00.186364+00:00
-- url     : https://prove2.me/submissions/3553c2ab-5655-48a6-be43-26a14f149cd4

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStrichartzWave

set_option autoImplicit false

noncomputable section

open BookProof.Starobinsky in
/-- Self-contained smoothness of the scalaron potential along a direction (same statement as the
platform's `contDiff_scalaronAlong`, proved here so the solution carries no imported stub). -/
theorem P2M59c758ef.contDiff_scalaronAlong_aux {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M alpha : ℝ) (e : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => starobinskyV M alpha (inner ℝ x e)) := by
  unfold starobinskyV
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => (inner ℝ x e : ℝ)) :=
    contDiff_id.inner ℝ contDiff_const
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => Real.exp (-(Real.sqrt (2 / 3)) * (inner ℝ x e : ℝ) / M)) :=
    Real.contDiff_exp.comp ((contDiff_const.mul h).div_const _)
  exact contDiff_const.mul ((contDiff_const.sub h2).pow 2)

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv in
/-- An operator on Schwartz space is formally symmetric in `L²`. -/
def P2M59c758ef.SchSym (n : ℕ) (T : 𝓢(SpaceTime n, ℂ) →L[ℂ] 𝓢(SpaceTime n, ℂ)) : Prop :=
  ∀ f g : 𝓢(SpaceTime n, ℂ),
    inner ℂ (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) (T f))
        (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) g) =
      inner ℂ (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) f)
        (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) (T g))

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv P2M59c758ef in
theorem P2M59c758ef.schSym_add (n : ℕ) {T S : 𝓢(SpaceTime n, ℂ) →L[ℂ] 𝓢(SpaceTime n, ℂ)}
    (hT : SchSym n T) (hS : SchSym n S) : SchSym n (T + S) := by
  intro f g
  simp only [add_apply, map_add, inner_add_left, inner_add_right]
  rw [hT, hS]

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv P2M59c758ef in
theorem P2M59c758ef.schSym_zero (n : ℕ) : SchSym n 0 := by
  intro f g
  simp

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv P2M59c758ef in
theorem P2M59c758ef.schSym_id (n : ℕ) : SchSym n (ContinuousLinearMap.id ℂ _) := by
  intro f g
  rfl

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv P2M59c758ef in
theorem P2M59c758ef.schSym_smul (n : ℕ) (c : ℝ) {T : 𝓢(SpaceTime n, ℂ) →L[ℂ] 𝓢(SpaceTime n, ℂ)}
    (hT : SchSym n T) : SchSym n ((c : ℂ) • T) := by
  intro f g
  simp only [ContinuousLinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [hT]

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv P2M59c758ef in
theorem P2M59c758ef.schSym_secondDeriv (n : ℕ) (m : SpaceTime n) :
    SchSym n (secondDeriv m) := by
  intro f g
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap
  have key : ∀ a b : ℂ, inner ℂ a b = L a b := by
    intro a b
    simp [L, mul_comm]
  have e1 := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := (volume : Measure (SpaceTime n)))
    f (∂_{m} g) L m
  have e2 := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := (volume : Measure (SpaceTime n)))
    (∂_{m} f) g L m
  simp only [toLpCLM_apply, inner_toL2_toL2_eq, key]
  simp only [secondDeriv, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]
  rw [e1, e2, neg_neg]

open MeasureTheory SchwartzMap BookProof.StrichartzWave LineDeriv P2M59c758ef in
theorem P2M59c758ef.schSym_waveOp (n : ℕ) (κ : ℝ) : SchSym n (waveOp n κ) := by
  unfold waveOp constCoeffOp
  refine schSym_add n ?_ (schSym_smul n κ (schSym_id n))
  refine Finset.sum_induction _ (SchSym n) (fun a b ha hb => schSym_add n ha hb)
    (schSym_zero n) ?_
  intro i _
  exact schSym_smul n _ (schSym_secondDeriv n _)

open MeasureTheory SchwartzMap BookProof.StrichartzWave BookProof.ScalaronEsa P2M59c758ef in
theorem P2M59c758ef.cc_coe (n : ℕ) (x : ccDomain (SpaceTime n)) :
    (x : Lp ℂ 2 (volume : Measure (SpaceTime n))) =
      toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
        (((ccEquiv (SpaceTime n)).symm x : ccSchwartz (SpaceTime n)) : 𝓢(SpaceTime n, ℂ)) := by
  conv_lhs => rw [← (ccEquiv (SpaceTime n)).apply_symm_apply x]
  rfl

open MeasureTheory SchwartzMap BookProof.StrichartzWave BookProof.ScalaronEsa P2M59c758ef in
theorem P2M59c758ef.waveCc_apply (n : ℕ) (x : ccDomain (SpaceTime n)) :
    waveCc n x = toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
        (waveOp n 0 (((ccEquiv (SpaceTime n)).symm x : ccSchwartz (SpaceTime n)) :
          𝓢(SpaceTime n, ℂ))) := by
  have h : (schwartzEquiv (SpaceTime n)).symm (Submodule.inclusion ccDomain_le_schwartzDomain x)
      = (((ccEquiv (SpaceTime n)).symm x : ccSchwartz (SpaceTime n)) : 𝓢(SpaceTime n, ℂ)) := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [Submodule.coe_inclusion, cc_coe]
    rfl
  simp only [waveCc, opL2, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  rfl

open MeasureTheory SchwartzMap BookProof.StrichartzWave BookProof.ScalaronEsa P2M59c758ef in
theorem P2M59c758ef.opCc_apply (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (x : ccDomain (SpaceTime n)) :
    opCc W hW x = toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
        (mulCc W hW ((ccEquiv (SpaceTime n)).symm x)) := rfl

open MeasureTheory SchwartzMap BookProof.StrichartzWave BookProof.ScalaronEsa P2M59c758ef in
theorem P2M59c758ef.mulCc_apply (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (f : ccSchwartz (SpaceTime n)) (z : SpaceTime n) :
    (mulCc W hW f : 𝓢(SpaceTime n, ℂ)) z = (W z : ℂ) * (f : 𝓢(SpaceTime n, ℂ)) z := rfl

open MeasureTheory SchwartzMap BookProof.StrichartzWave BookProof.ScalaronEsa P2M59c758ef in
theorem P2M59c758ef.mulCc_sym (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (f g : ccSchwartz (SpaceTime n)) :
    inner ℂ (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) (mulCc W hW f))
        (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) (g : 𝓢(SpaceTime n, ℂ))) =
      inner ℂ (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) (f : 𝓢(SpaceTime n, ℂ)))
        (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n)) (mulCc W hW g)) := by
  simp only [toLpCLM_apply, inner_toL2_toL2_eq, mulCc_apply]
  congr 1
  funext z
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

open MeasureTheory SchwartzMap BookProof.StrichartzWave BookProof.ScalaronEsa BookProof.FarisLavine P2M59c758ef in
theorem P2M59c758ef.waveAddSmooth_symm (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) := by
  intro x y
  simp only [waveAddSmoothPotential, LinearMap.add_apply, inner_add_left, inner_add_right]
  congr 1
  · rw [waveCc_apply, waveCc_apply, cc_coe, cc_coe]
    exact schSym_waveOp n 0 _ _
  · have hx := cc_coe n x
    have hy := cc_coe n y
    have ox := opCc_apply n W hW x
    have oy := opCc_apply n W hW y
    have key := mulCc_sym n W hW ((ccEquiv (SpaceTime n)).symm x) ((ccEquiv (SpaceTime n)).symm y)
    calc inner ℂ (opCc W hW x) (y : Lp ℂ 2 (volume : Measure (SpaceTime n)))
        = inner ℂ (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
            (mulCc W hW ((ccEquiv (SpaceTime n)).symm x)))
            (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
              (((ccEquiv (SpaceTime n)).symm y : ccSchwartz (SpaceTime n)) :
                𝓢(SpaceTime n, ℂ))) := congrArg₂ (fun a b => inner ℂ a b) ox hy
      _ = inner ℂ (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
              (((ccEquiv (SpaceTime n)).symm x : ccSchwartz (SpaceTime n)) :
                𝓢(SpaceTime n, ℂ)))
            (toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime n))
              (mulCc W hW ((ccEquiv (SpaceTime n)).symm y))) := key
      _ = inner ℂ (x : Lp ℂ 2 (volume : Measure (SpaceTime n))) (opCc W hW y) :=
          (congrArg₂ (fun a b => inner ℂ a b) hx oy).symm

open BookProof.Starobinsky BookProof.StrichartzWave BookProof.ScalaronEsa BookProof.FarisLavine BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow BookProof.ChapterStoneResolvent BookProof.EsaClosure in
theorem solution (n : ℕ) (M alpha : ℝ) (e : SpaceTime n) :
    SymmetricOn (ccDomain (SpaceTime n))
      (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
        (P2M59c758ef.contDiff_scalaronAlong_aux M alpha e)) := by
  exact P2M59c758ef.waveAddSmooth_symm n _ _

end
