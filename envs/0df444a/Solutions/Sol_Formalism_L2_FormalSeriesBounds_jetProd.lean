-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jetProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:09.734344+00:00
-- url     : https://prove2.me/submissions/9093561c-e041-4ec5-b2bb-67ddc98c24d2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_supported
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_mvExp_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_valOf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rowCopy_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_rowCopy
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_grAll_pl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : JetProdSt := by
  intro C _ d I _ hL N K what₂ pl hpl P kind gr
  have hkind : ∀ s : (Σ i : Fin K, Fin (what₂ i)), kindAll pl kind (pl s) = kind s.1 s.2 := by
    intro s
    unfold kindAll
    have h : ∃ s', pl s' = pl s := ⟨s, rfl⟩
    rw [dif_pos h]
    have hs : h.choose = s := hpl h.choose_spec
    rw [hs]
  have hout : ∀ ρ : Fin N, ρ ∉ Finset.univ.image pl →
      rowCopy ρ (grAll pl gr ρ) * mvExp (rowCopy ρ (rtjH hL (kindAll pl kind ρ))) = 1 := by
    intro ρ hρ
    have h : ¬ ∃ s, pl s = ρ := by
      rintro ⟨s, rfl⟩
      exact hρ (Finset.mem_image_of_mem pl (Finset.mem_univ s))
    have h1 : grAll pl gr ρ = 1 := by
      unfold grAll
      rw [dif_neg h]
    have h2 : kindAll pl kind ρ = none := by
      unfold kindAll
      rw [dif_neg h]
    rw [h1, h2, rtj_rowCopy_eq, rtj_rowCopy_eq]
    simp only [rtjH, map_one, map_zero, rtj_mvExp_zero, mul_one]
  have hreindex : ∀ f : Fin N → MvPowerSeries (Fin N × WV I) C, (∀ ρ ∉ Finset.univ.image pl, f ρ = 1) →
      ∏ ρ, f ρ = ∏ i, ∏ r : Fin (what₂ i), f (pl ⟨i, r⟩) := by
    intro f hf
    rw [← Finset.prod_subset (Finset.subset_univ _) (fun ρ _ hρ => hf ρ hρ),
      Finset.prod_image (by intro x _ y _ h; exact hpl h)]
    exact Fintype.prod_sigma (fun s => f (pl s))
  have hblk : ∀ i, MvPowerSeries.rename (rtjE (I := I) hpl i)
        (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r))))) =
      ∏ r, (rowCopy (pl ⟨i, r⟩) (grAll pl gr (pl ⟨i, r⟩)) *
        mvExp (rowCopy (pl ⟨i, r⟩) (rtjH hL (kindAll pl kind (pl ⟨i, r⟩))))) := by
    intro i
    rw [map_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [map_mul, rtj_rename_mvExp, rtj_rename_rowCopy, rtj_rename_rowCopy, rtj_grAll_pl hpl gr ⟨i, r⟩,
      hkind ⟨i, r⟩]
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin K)), ∀ j ∈ (Finset.univ : Finset (Fin K)), i ≠ j →
      Disjoint (Set.range (rtjE (I := I) hpl i)) (Set.range (rtjE (I := I) hpl j)) := by
    intro i _ j _ hij
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    apply hij
    have h1 : pl ⟨j, y.1⟩ = pl ⟨i, x.1⟩ := congrArg Prod.fst hy
    exact (congrArg Sigma.fst (hpl h1)).symm
  simp only [rtj_valOf]
  calc jetAt0 (prodAll pl P)
        (∏ ρ, (rowCopy ρ (grAll pl gr ρ) * mvExp (rowCopy ρ (rtjH hL (kindAll pl kind ρ)))))
      = jetAt0 (∏ i, MvPolynomial.rename (rtjE (I := I) hpl i) (P i))
          (∏ i, MvPowerSeries.rename (rtjE (I := I) hpl i)
            (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r)))))) := by
        refine congrArg₂ jetAt0 rfl ?_
        rw [hreindex _ hout]
        exact Finset.prod_congr rfl fun i _ => (hblk i).symm
    _ = ∏ i, jetAt0 (MvPolynomial.rename (rtjE (I := I) hpl i) (P i)) (MvPowerSeries.rename (rtjE (I := I) hpl i)
            (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r)))))) :=
        rtj_jet_prod (fun i => Set.range (rtjE (I := I) hpl i)) Finset.univ hdis
          (fun i => MvPolynomial.rename (rtjE (I := I) hpl i) (P i))
          (fun i => MvPowerSeries.rename (rtjE (I := I) hpl i)
            (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r))))))
          (fun i _ => rtj_rename_supported _ _) (fun i _ => rtj_serIn_rename _ _)
    _ = ∏ i, jetAt0 (P i) (∏ r, (rowCopy r (gr i r) * mvExp (rowCopy r (rtjH hL (kind i r))))) :=
        Finset.prod_congr rfl fun i _ => rtj_jet_rename _ _ _
end Formalism.L2.FormalSeriesBounds
