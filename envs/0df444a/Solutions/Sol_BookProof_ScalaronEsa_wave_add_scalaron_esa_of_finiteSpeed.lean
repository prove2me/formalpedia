-- Prove2me | solution 1 for BookProof.ScalaronEsa.wave_add_scalaron_esa_of_finiteSpeed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:30:03.512353+00:00
-- url     : https://prove2.me/submissions/f0e8fd1f-db49-47b3-b4dc-58e48990cc3a

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
theorem P2M3fd12997.contDiff_scalaronAlong_aux {E : Type*} [NormedAddCommGroup E]
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

open BookProof.Starobinsky BookProof.StrichartzWave BookProof.ScalaronEsa BookProof.FarisLavine BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow BookProof.ChapterStoneResolvent BookProof.EsaClosure P2M3fd12997 in
theorem solution (n : ℕ) (M alpha : ℝ) (e : SpaceTime n)
    (finiteSpeed : ∀ z : ℂ, z.im ≠ 0 →
      DeficiencyTrivialAt (ccDomain (SpaceTime n))
        (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
          (contDiff_scalaronAlong_aux M alpha e)) z) :
    EssentiallySelfAdjointOn (ccDomain (SpaceTime n))
      (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
        (contDiff_scalaronAlong_aux M alpha e)) := by
  exact ⟨finiteSpeed _ (by simp), finiteSpeed _ (by simp)⟩

end

#print axioms solution
