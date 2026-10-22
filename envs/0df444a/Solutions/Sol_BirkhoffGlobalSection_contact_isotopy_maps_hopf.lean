-- Prove2me | solution 1 for BirkhoffGlobalSection.contact_isotopy_maps_hopf
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T04:40:18.032734+00:00
-- url     : https://prove2.me/submissions/bddbbedb-af0f-4276-8ac0-d1fba72dd366

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Tactic

open BirkhoffGlobalSection
open scoped ContDiff

private def hopfLinear : Plane →L[ℝ] Phase :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj (0 : Fin 2), 0,
      -ContinuousLinearMap.proj (1 : Fin 2), 0]

private theorem hopfLinear_apply (u : Plane) :
    hopfLinear u = standardHopfCircle u := by
  ext i
  fin_cases i <;> simp [hopfLinear, standardHopfCircle]

private theorem hopf_smooth : ContDiff ℝ ∞ standardHopfCircle := by
  have heq : standardHopfCircle = (hopfLinear : Plane → Phase) := by
    funext u
    exact (hopfLinear_apply u).symm
  rw [heq]
  exact hopfLinear.contDiff

private theorem hopf_fderiv (u v : Plane) :
    fderiv ℝ standardHopfCircle u v = standardHopfCircle v := by
  have heq : standardHopfCircle = (hopfLinear : Plane → Phase) := by
    funext w
    exact (hopfLinear_apply w).symm
  rw [heq, ContinuousLinearMap.fderiv]

private theorem hopf_sphere (u : Plane) (hu : u ∈ unitCircle) :
    standardHopfCircle u ∈ unitThreeSphere := by
  simpa [unitThreeSphere, zNormSq, wNormSq, standardHopfCircle,
    unitCircle, planeNormSq] using hu

private theorem hopf_contact (u : Plane) (hu : u ∈ unitCircle) :
    phaseRadialContact (standardHopfCircle u)
      (standardHopfCircle (circleTangent u)) = 1 / 2 := by
  have hu' : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
  simp [phaseRadialContact, phaseSymplecticForm, standardHopfCircle,
    circleTangent]
  nlinarith

theorem solution (F : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (F.toFun '' (standardHopfCircle '' unitCircle))) := by
  refine ⟨{
    isotopy := fun p => (I.slice p.1).toFun (standardHopfCircle p.2)
    smooth := ?_
    sphere := ?_
    injective := ?_
    antipodal := ?_
    positive := ?_
    start := ?_
    finish := ?_
  }⟩
  · intro t ht u hu
    exact (I.smooth t ht _ (hopf_sphere u hu)).comp (t, u)
      (contDiffAt_fst.prodMk (hopf_smooth.contDiffAt.comp (t, u) contDiffAt_snd))
  · intro t ht u hu
    exact (I.slice t).maps_sphere (hopf_sphere u hu)
  · intro t ht u hu v hv huv
    have heq := congrArg (I.slice t).invFun huv
    rw [(I.slice t).left_inv _ (hopf_sphere u hu),
      (I.slice t).left_inv _ (hopf_sphere v hv)] at heq
    have hzero := congrFun heq (0 : Fin 4)
    have hone := congrFun heq (2 : Fin 4)
    ext i
    fin_cases i
    · simpa [standardHopfCircle] using hzero
    · simpa [standardHopfCircle] using hone
  · intro t ht u hu
    have hneg : standardHopfCircle (-u) = -standardHopfCircle u := by
      ext i
      fin_cases i <;> simp [standardHopfCircle]
    change (I.slice t).toFun (standardHopfCircle (-u)) = _
    rw [hneg, (I.slice t).antipodal _ (hopf_sphere u hu)]
  · intro t ht u hu
    obtain ⟨a, ha, hcontact⟩ := (I.slice t).contact _ (hopf_sphere u hu)
    have htangent : phaseDot (standardHopfCircle u)
        (standardHopfCircle (circleTangent u)) = 0 := by
      simp [phaseDot, standardHopfCircle, circleTangent]
      ring
    have hdF := ((I.slice t).smooth _ (hopf_sphere u hu)).differentiableAt
      (by simp)
    have hdh := hopf_smooth.differentiable (by simp)
    change 0 < phaseRadialContact ((I.slice t).toFun (standardHopfCircle u))
      (fderiv ℝ ((I.slice t).toFun ∘ standardHopfCircle) u (circleTangent u))
    rw [fderiv_comp u hdF (hdh u), ContinuousLinearMap.comp_apply,
      hopf_fderiv, hcontact _ htangent, hopf_contact u hu]
    positivity
  · intro u hu
    exact I.start _ (hopf_sphere u hu)
  · ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (I.slice 1).toFun (standardHopfCircle u) ∈ _
      rw [I.finish _ (hopf_sphere u hu)]
      exact ⟨standardHopfCircle u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, I.finish _ (hopf_sphere u hu)⟩
