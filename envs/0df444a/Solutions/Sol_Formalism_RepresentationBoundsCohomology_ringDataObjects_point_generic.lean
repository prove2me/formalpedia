-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.point_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:45.481299+00:00
-- url     : https://prove2.me/submissions/aa997cd9-c682-43a5-93b2-3db92bf35c7a

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_blockPoly_factor
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_pencil_choose
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_clearDen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_blockDiag_of_mem
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_idem_factor
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_sepPoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution (hD : StatDensity) (hC : StatCornerSimple) {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {X : Type} [Fintype X] (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (eB : X → Matrix d d O) (heBm : eB ∈ tSpan T r)
    (heBB : eB * eB = eB) (x : X) (m : ℕ) (c : d → Fin m) (P : Matrix d d (FractionRing O))
    (hG : BlockDiagonalIrreducibleAt (fun g => (r g x).map (algebraMap O (FractionRing O))) m c P) (S0 : Matrix d d O) (w : O)
    (hw : w ≠ 0) :
    ∃ (j : X → O) (a : X → Matrix d d O), j ∈ T ∧ (∀ y, y ≠ x → j y = 0) ∧ a ∈ tSpan T r ∧
      (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
        ((eB x * S0 * eB x + w • (j x • (eB x * a x * eB x))).map
          (algebraMap O (FractionRing O)))).Separable := by
  classical
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hOinf : Infinite O := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    exact Infinite.of_injective (fun k : ℕ => ϖ ^ k)
      (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)
  have hKinf : Infinite (FractionRing O) := Infinite.of_injective _ hφ
  have he : (eB x).map (algebraMap O (FractionRing O)) * (eB x).map (algebraMap O (FractionRing O)) =
      (eB x).map (algebraMap O (FractionRing O)) := by
    rw [← Matrix.map_mul, ← Pi.mul_apply eB eB x, heBB]
  have heblk := blockDiag_of_mem T r x c P hG.2.1 eB heBm
  obtain ⟨A, hAblk, hAsep⟩ := hC (FractionRing O) d m c P _ hG.1 he heblk
  let ρ : G →* Matrix d d (FractionRing O) :=
    ((algebraMap O (FractionRing O)).mapMatrix : Matrix d d O →+* Matrix d d (FractionRing O)).toMonoidHom.comp
      ((Pi.evalMonoidHom (fun _ : X => Matrix d d O) x).comp r)
  have hAspan : A ∈ Submodule.span (FractionRing O)
      (Set.range fun g => (r g x).map (algebraMap O (FractionRing O))) :=
    hD (FractionRing O) d G ρ m c P hG A hAblk
  obtain ⟨b, hb0, a, ha, hab⟩ := clearDen T r x A hAspan
  obtain ⟨f, hfT, hfx, hfy⟩ := sepPoint O X T hsep x
  obtain ⟨S, hS1, hS2, U, W, hUW, hWU⟩ := idem_factor _ he
  have hfac : ∀ M : Matrix d d (FractionRing O),
      blockPoly ((eB x).map (algebraMap O (FractionRing O)))
        ((eB x).map (algebraMap O (FractionRing O)) * M * (eB x).map (algebraMap O (FractionRing O))) =
      (W * M * U).charpoly := by
    intro M
    have h1 := blockPoly_factor U W hWU (W * M * U)
    rw [hUW] at h1
    rw [← h1, ← hUW]
    simp only [Matrix.mul_assoc]
  have hB1 : (W * A * U).charpoly.Separable := by rw [← hfac]; exact hAsep
  set c0 : FractionRing O := algebraMap O (FractionRing O) w * algebraMap O (FractionRing O) (f x) *
    algebraMap O (FractionRing O) b with hc0def
  have hc0 : c0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero_iff _ hφ).mpr hw) ((map_ne_zero_iff _ hφ).mpr hfx))
      ((map_ne_zero_iff _ hφ).mpr hb0)
  obtain ⟨l, hl⟩ := pencil_choose hφ (W * S0.map (algebraMap O (FractionRing O)) * U) (W * A * U) hB1 c0 hc0
  refine ⟨fun y => f y * l, a, T.mul_mem hfT (T.algebraMap_mem l), fun y hy => by simp [hfy y hy], ha, ?_⟩
  have hs : ∀ (t : O) (N : Matrix d d O),
      (t • N).map (algebraMap O (FractionRing O)) = algebraMap O (FractionRing O) t • N.map (algebraMap O (FractionRing O)) :=
    fun t N => by ext; simp
  have hadd : ∀ N N' : Matrix d d O, (N + N').map (algebraMap O (FractionRing O)) =
      N.map (algebraMap O (FractionRing O)) + N'.map (algebraMap O (FractionRing O)) :=
    fun N N' => by ext; simp
  have hM : (eB x * S0 * eB x + w • ((f x * l) • (eB x * a x * eB x))).map (algebraMap O (FractionRing O)) =
      (eB x).map (algebraMap O (FractionRing O)) *
        (S0.map (algebraMap O (FractionRing O)) + (c0 * algebraMap O (FractionRing O) l) • A) *
        (eB x).map (algebraMap O (FractionRing O)) := by
    rw [hadd, hs, hs, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hab]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul]
    congr 2
    rw [hc0def]
    ring
  beta_reduce
  rw [hM, hfac, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  exact hl
end Formalism.RepresentationBoundsCohomology.ringDataObjects
