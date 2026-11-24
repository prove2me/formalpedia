-- Prove2me | solution 1 for Formalism.IndefR.U2.decompOfNormal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.889418+00:00
-- url     : https://prove2.me/submissions/6b0bc132-3837-4968-9ca6-5d38fd77448c

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped InnerProductSpace
namespace Formalism.IndefR.U2
private lemma adjoint_apply_eq_conj_smul_of_eigen {I A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (op : I → Module.End ℂ A) (hc : PairCommF op) (ha : AdjClosed op)
    (i : I) (μ : ℂ) (y : A) (hy : op i y = μ • y) :
    LinearMap.adjoint (op i) y = (starRingEnd ℂ) μ • y := by
  obtain ⟨i', hi'⟩ := ha i
  have hcomm : op i (LinearMap.adjoint (op i) y) = LinearMap.adjoint (op i) (op i y) := by
    rw [← hi']
    exact LinearMap.congr_fun (hc i i').eq y
  have hTv : op i (LinearMap.adjoint (op i) y - (starRingEnd ℂ) μ • y)
      = μ • (LinearMap.adjoint (op i) y - (starRingEnd ℂ) μ • y) := by
    rw [map_sub, map_smul, hcomm, hy, map_smul, smul_sub, smul_comm μ ((starRingEnd ℂ) μ) y]
  have h0 : ⟪LinearMap.adjoint (op i) y - (starRingEnd ℂ) μ • y,
      LinearMap.adjoint (op i) y - (starRingEnd ℂ) μ • y⟫_ℂ = 0 := by
    rw [inner_sub_left, LinearMap.adjoint_inner_left, hTv, inner_smul_left, inner_smul_right]
    simp
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
private lemma mem_eigPart_iff' {I A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (op : I → Module.End ℂ A) (c : I → ℂ) (x : A) :
    x ∈ eigPart op c ↔ ∀ i, op i x = c i • x := by
  simp [eigPart, sub_eq_zero]
private lemma inner_eq_zero_of_mem_eigPart_ne {I A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (op : I → Module.End ℂ A) (hc : PairCommF op) (ha : AdjClosed op)
    {c c' : I → ℂ} (hcc : c ≠ c') {x y : A} (hx : x ∈ eigPart op c) (hy : y ∈ eigPart op c') :
    ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hcc
  have hx' := (mem_eigPart_iff' op c x).mp hx i
  have hy' := adjoint_apply_eq_conj_smul_of_eigen op hc ha i (c' i) y ((mem_eigPart_iff' op c' y).mp hy i)
  have h1 : ⟪op i x, y⟫_ℂ = ⟪x, LinearMap.adjoint (op i) y⟫_ℂ :=
    (LinearMap.adjoint_inner_right (op i) x y).symm
  rw [hx', hy', inner_smul_left, inner_smul_right] at h1
  by_contra hz
  exact hi ((starRingEnd ℂ).injective (mul_right_cancel₀ hz h1))
private lemma iSup_eigPart_inf_mono {I A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (op : I → Module.End ℂ A) {W W' : Submodule ℂ A} (h : W' ≤ W) :
    (⨆ c ∈ Occ op W', eigPart op c ⊓ W') ≤ ⨆ c ∈ Occ op W, eigPart op c ⊓ W := by
  refine iSup₂_le fun c hc => le_iSup₂_of_le c ?_ (inf_le_inf_left _ h)
  have hc' : eigPart op c ⊓ W' ≠ ⊥ := hc
  change eigPart op c ⊓ W ≠ ⊥
  intro h0
  apply hc'
  rw [eq_bot_iff] at h0 ⊢
  exact (inf_le_inf_left _ h).trans h0
private lemma le_iSup_eigPart_inf_of_invariant {I A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (op : I → Module.End ℂ A) (hc : PairCommF op) (ha : AdjClosed op)
    (n : ℕ) : ∀ W : Submodule ℂ A, Module.finrank ℂ W = n → (∀ i, ∀ x ∈ W, op i x ∈ W) →
      W ≤ ⨆ c ∈ Occ op W, eigPart op c ⊓ W := by
  induction' n using Nat.strong_induction_on with n ih
  intro W hn hW
  by_cases hbot : W = ⊥
  · rw [hbot]
    exact bot_le
  by_cases hsc : ∀ i, ∃ μ : ℂ, ∀ x ∈ W, op i x = μ • x
  · choose c hc' using hsc
    have hle : W ≤ eigPart op c := fun x hx => (mem_eigPart_iff' op c x).mpr fun i => hc' i x hx
    have hocc : c ∈ Occ op W := by
      change eigPart op c ⊓ W ≠ ⊥
      rw [inf_eq_right.mpr hle]
      exact hbot
    exact le_iSup₂_of_le c hocc (le_inf hle le_rfl)
  push_neg at hsc
  obtain ⟨i, hi⟩ := hsc
  have hex : ∃ μ : ℂ, ∃ v : A, v ∈ W ∧ v ≠ 0 ∧ op i v = μ • v := by
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hbot
    have hmaps : ∀ x ∈ W, op i x ∈ W := hW i
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((op i).restrict hmaps)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine ⟨μ, v, v.2, ?_, ?_⟩
    · intro h
      exact hv.2 (Subtype.ext h)
    · have h := congrArg Subtype.val hv.apply_eq_smul
      simpa using h
  obtain ⟨μ, v, hvW, hv0, hv1⟩ := hex
  obtain ⟨x0, hx0W, hx0⟩ := hi μ
  obtain ⟨W1, hW1⟩ : ∃ W1 : Submodule ℂ A, ∀ x, x ∈ W1 ↔ x ∈ W ∧ op i x = μ • x :=
    ⟨W ⊓ LinearMap.ker (op i - μ • 1), fun x => by simp [sub_eq_zero]⟩
  have hW1W : W1 ≤ W := fun x hx => ((hW1 x).mp hx).1
  have hvW1 : v ∈ W1 := (hW1 v).mpr ⟨hvW, hv1⟩
  have hW1inv : ∀ j, ∀ x ∈ W1, op j x ∈ W1 := by
    intro j x hx
    obtain ⟨hxW, hxe⟩ := (hW1 x).mp hx
    refine (hW1 _).mpr ⟨hW j x hxW, ?_⟩
    have hcomm : op i (op j x) = op j (op i x) := LinearMap.congr_fun (hc i j).eq x
    rw [hcomm, hxe, map_smul]
  have hW2inv : ∀ j, ∀ x ∈ W1ᗮ ⊓ W, op j x ∈ W1ᗮ ⊓ W := by
    intro j x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨?_, hW j x hx2⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨j', hj'⟩ := ha j
    rw [← LinearMap.adjoint_inner_left, ← hj']
    exact Submodule.inner_right_of_mem_orthogonal (hW1inv j' u hu) hx1
  have hsup : W ≤ W1 ⊔ W1ᗮ ⊓ W := by
    intro x hx
    first
    | (rw [Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hW1W]; exact hx)
    | (obtain ⟨y, hy, z, hz, rfl⟩ := W1.exists_add_mem_mem_orthogonal x
       exact Submodule.add_mem_sup hy
        (Submodule.mem_inf.mpr ⟨hz, (W.add_mem_iff_right (hW1W hy)).mp hx⟩))
    | (exact Submodule.mem_sup.mpr ⟨(orthogonalProjection W1 x : A), (orthogonalProjection W1 x).2,
        x - orthogonalProjection W1 x, Submodule.mem_inf.mpr
          ⟨sub_orthogonalProjection_mem_orthogonal x, W.sub_mem hx (hW1W (orthogonalProjection W1 x).2)⟩,
        by abel⟩)
    | (exact Submodule.mem_sup.mpr ⟨(W1.orthogonalProjection x : A), (W1.orthogonalProjection x).2,
        x - W1.orthogonalProjection x, Submodule.mem_inf.mpr
          ⟨W1.sub_orthogonalProjection_mem_orthogonal x,
            W.sub_mem hx (hW1W (W1.orthogonalProjection x).2)⟩,
        by abel⟩)
  have hlt1 : W1 < W := by
    refine lt_of_le_of_ne hW1W fun h => hx0 ?_
    have hx0' : x0 ∈ W1 := by
      rw [h]
      exact hx0W
    exact ((hW1 x0).mp hx0').2
  have hlt2 : W1ᗮ ⊓ W < W := by
    refine lt_of_le_of_ne inf_le_right fun h => hv0 ?_
    have hv2 : v ∈ W1ᗮ ⊓ W := by
      rw [h]
      exact hvW
    exact inner_self_eq_zero.mp
      (Submodule.inner_right_of_mem_orthogonal hvW1 (Submodule.mem_inf.mp hv2).1)
  have hr1 : Module.finrank ℂ W1 < n := by
    rw [← hn]
    exact Submodule.finrank_lt_finrank_of_lt hlt1
  have hr2 : Module.finrank ℂ (W1ᗮ ⊓ W : Submodule ℂ A) < n := by
    rw [← hn]
    exact Submodule.finrank_lt_finrank_of_lt hlt2
  have h1 := ih _ hr1 W1 rfl hW1inv
  have h2 := ih _ hr2 (W1ᗮ ⊓ W) rfl hW2inv
  exact hsup.trans (sup_le (h1.trans (iSup_eigPart_inf_mono op hW1W))
    (h2.trans (iSup_eigPart_inf_mono op inf_le_right)))
end Formalism.IndefR.U2
end

set_option autoImplicit false
open scoped InnerProductSpace
open Formalism Formalism.IndefR Formalism.IndefR.U2
namespace Formalism.IndefR.U2
theorem _root_.solution : DecompOfNormalStatement := by
  intro I A _ _ _ op good hc ha hgood
  exact ⟨le_iSup_eigPart_inf_of_invariant op hc ha _ good rfl hgood, fun c _ c' _ hcc x hx y hy =>
    inner_eq_zero_of_mem_eigPart_ne op hc ha hcc (Submodule.mem_inf.mp hx).1 (Submodule.mem_inf.mp hy).1⟩
end Formalism.IndefR.U2
