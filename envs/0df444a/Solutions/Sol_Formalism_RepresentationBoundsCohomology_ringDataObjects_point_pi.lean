-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.point_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:52:21.092902+00:00
-- url     : https://prove2.me/submissions/978a2f6c-57f6-46af-83ca-33d55bc49f05

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple

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
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ) (hP : PrimHyp O T r π bl χ₁ ε) (eB : X → Matrix d d O)
    (heBπ : eB π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1)) (g₀ : G)
    (hε : ∀ i j : ℕ, i < t → j < t → (ε g₀) ^ i = (ε g₀) ^ j → i = j) :
    (blockPoly ((eB π).map (algebraMap O (FractionRing O)))
      ((eB π * r g₀ π * eB π).map (algebraMap O (FractionRing O)))).Separable := by
  classical
  obtain ⟨-, -, -, hblk, hcard, hdiag⟩ := hP
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  set φ := algebraMap O (FractionRing O) with hφdef
  set lam : d → FractionRing O := fun a => if bl a = 0 then 0 else
    φ ((χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ ((bl a : ℕ) - 1) : Oˣ) : O)) with hlam
  have hone : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hbl
    have h2 := Fintype.card_le_one_iff.mp (hcard (bl a) ha).le ⟨a, rfl⟩ ⟨b, hbl.symm⟩
    exact congrArg Subtype.val h2
  have he : (eB π).map φ = Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1) := by
    rw [heBπ]
    ext i j
    rcases eq_or_ne i j with rfl | h
    · by_cases h0 : bl i = 0 <;> simp [h0]
    · simp [h]
  have hA : (eB π * r g₀ π * eB π).map φ = Matrix.diagonal lam := by
    ext a b
    rw [Matrix.map_apply, heBπ, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases eq_or_ne a b with rfl | hab
    · by_cases h0 : bl a = 0
      · simp [h0, hlam]
      · simp [h0, hlam, hdiag g₀ a h0]
    · rw [Matrix.diagonal_apply_ne _ hab]
      by_cases ha0 : bl a = 0
      · simp [ha0]
      by_cases hb0 : bl b = 0
      · simp [hb0]
      have hne : bl a ≠ bl b := fun hbl => hab (hone a b ha0 hbl)
      simp [hblk g₀ a b hne]
  rw [he, hA]
  have hm : (Polynomial.X : Polynomial (FractionRing O)) •
        (Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1)).map Polynomial.C -
        (Matrix.diagonal lam).map Polynomial.C +
        (1 - Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1)).map Polynomial.C =
      Matrix.diagonal (fun a => if bl a = 0 then 1 else Polynomial.X - Polynomial.C (lam a)) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · by_cases h0 : bl i = 0 <;> simp [h0, hlam]
    · simp [h, Matrix.one_apply_ne h]
  have hbp : blockPoly (Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1))
      (Matrix.diagonal lam) =
      ∏ a ∈ Finset.univ.filter (fun a => bl a ≠ 0), (Polynomial.X - Polynomial.C (lam a)) := by
    unfold blockPoly
    rw [hm, Matrix.det_diagonal, Finset.prod_filter]
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases h0 : bl a = 0 <;> simp [h0]
  rw [hbp, Polynomial.separable_prod_X_sub_C_iff']
  intro a ha0 b hb0 hlab
  have ha : bl a ≠ 0 := (Finset.mem_filter.mp ha0).2
  have hb : bl b ≠ 0 := (Finset.mem_filter.mp hb0).2
  simp only [hlam, if_neg ha, if_neg hb] at hlab
  have h1 := mul_left_cancel₀ (Units.ne_zero (χ₁ g₀)) (hφ hlab)
  have h2 : (ε g₀)⁻¹ ^ ((bl a : ℕ) - 1) = (ε g₀)⁻¹ ^ ((bl b : ℕ) - 1) := Units.ext h1
  rw [inv_pow, inv_pow, inv_inj] at h2
  have ha' : (bl a : ℕ) ≠ 0 := fun h => ha (by ext; simpa using h)
  have hb' : (bl b : ℕ) ≠ 0 := fun h => hb (by ext; simpa using h)
  have hia : (bl a : ℕ) - 1 < t := by have := (bl a).isLt; omega
  have hib : (bl b : ℕ) - 1 < t := by have := (bl b).isLt; omega
  have h3 := hε _ _ hia hib h2
  exact hone a b ha (Fin.ext (by omega))
end Formalism.RepresentationBoundsCohomology.ringDataObjects
