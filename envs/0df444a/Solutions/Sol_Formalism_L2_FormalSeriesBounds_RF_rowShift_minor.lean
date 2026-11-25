-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rowShift_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:38.545749+00:00
-- url     : https://prove2.me/submissions/cda1c027-f3ca-4055-b924-a0dd1a91a8cd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_keyL_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
section Atom
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
private theorem det_mapMatrix_shear_eq_det {K : ℕ} (A : Matrix (Fin K) (Fin K) (MvPolynomial (Letter T r n) C))
    (μ : Fin K → Fin K → Letter T r n) (hA : ∀ b c, A b c = X (μ b c)) (σ0 : T) (κ : Fin K → Fin n)
    (hμ : ∀ b c, keyL (μ b c) = (σ0, c.val, κ b)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    ((rowShift r n C σ i i' t).mapMatrix A).det = A.det := by
  have h3 : ∀ b c, (μ b c).snd.2 = κ b := fun b c => congrArg (fun p => p.2.2) (hμ b c)
  by_cases hc : σ = σ0 ∧ i.val < K
  · obtain ⟨hσ, hiK⟩ := hc
    subst σ0
    have hi'K : i'.val < K := lt_trans hi hiK
    let c0 : Fin K := ⟨i.val, hiK⟩
    let c1 : Fin K := ⟨i'.val, hi'K⟩
    have hne : c0 ≠ c1 := by
      intro h
      have h' := congrArg Fin.val h
      exact hi.ne' (Fin.ext h')
    have h1 : ∀ b, μ b c1 = ⟨σ, (i', κ b)⟩ := fun b =>
      keyL_inj (show keyL (μ b c1) = keyL ⟨σ, (i', κ b)⟩ from hμ b c1)
    have hmat : (rowShift r n C σ i i' t).mapMatrix A =
        A.updateCol c0 (fun b => A b c0 + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b c1) := by
      ext b c
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply, hA, rowShift_X, hμ, h3, h1]
      by_cases hcc : c = c0
      · have hv : (c : ℕ) = i.val := by rw [hcc]
        rw [if_pos (by rw [hv]), if_pos hcc, hcc, smul_eq_mul]
      · have hv : (c : ℕ) ≠ i.val := fun h => hcc (Fin.ext h)
        rw [if_neg (by simp [hv]), if_neg hcc]
    rw [hmat]
    exact Matrix.det_updateCol_add_smul_self A hne (MvPolynomial.C t : MvPolynomial (Letter T r n) C)
  · congr 1
    ext b c
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, hA, rowShift_X, hμ, h3]
    rw [if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hc ⟨h.1.symm, by rw [← h.2.1]; exact c.isLt⟩
end Atom
section Fam
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}
end Fam
end Formalism.L2.FormalSeriesBounds.RF
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {N N' : ℕ} (lam : Fin N × Fin N' → Letter T r n) (σ0 : T) (col : Fin N → Fin n)
    (hlam : ∀ ρ c, keyL (lam (ρ, c)) = (σ0, c.val, col ρ)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (rename lam (minorK C N N' k)) = rename lam (minorK C N N' k) := by
  unfold minorK
  split_ifs with hk
  · rw [AlgHom.map_det, AlgHom.map_det]
    exact det_mapMatrix_shear_eq_det _ (fun b c => lam (Fin.castLE hk.1 b, Fin.castLE hk.2 c))
      (fun b c => by simp [rename_X]) σ0 (fun b => col (Fin.castLE hk.1 b))
      (fun b c => hlam (Fin.castLE hk.1 b) (Fin.castLE hk.2 c)) σ i i' hi t
  · simp
end Formalism.L2.FormalSeriesBounds.RF
