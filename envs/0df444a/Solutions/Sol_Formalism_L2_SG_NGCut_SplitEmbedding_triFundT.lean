-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.triFundT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:34:30.322782+00:00
-- url     : https://prove2.me/submissions/cfbb1799-4b32-4a51-88dd-bd2312225c39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFund
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_box_fundT
import Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_shear_mp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution (P : Type) [Fintype P] [DecidableEq P] (α : P → Type) [∀ p, AddCommGroup (α p)]
    [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
    (hBm : ∀ p, Measurable (fun z : (∀ q, α q) × (∀ q, α q) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : ∀ q, α q), B p x 0 = 0)
    (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (A : ∀ p, AddSubgroup (α p)) [∀ p, Countable (A p)]
    (hinv : ∀ γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) → ∃ γ' : ∀ q, α q, (∀ p, γ' p - τ p γ' ∈ A p) ∧
      ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (F : ∀ p, Set (α p)) (hF : ∀ p, MeasurableSet (F p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
    (K : Set (∀ p, α p)) (hK : MeasurableSet K)
    (hKd : ∀ g, ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ mlaw B γ g ∈ K) :
    Measure.pi μ K = ∏ p, μ p (F p) := by
  classical
  set T : (∀ q, α q) → (∀ q, α q) → (∀ q, α q) := fun γ g => mlaw B γ g with hTdef
  have hT : ∀ γ, MeasurePreserving (T γ) (Measure.pi μ) (Measure.pi μ) := by
    intro γ
    have := shear_mp (Fintype.card P) P rfl α μ h (fun p g => γ p + B p γ g)
      (fun p => measurable_const.add ((hBm p).comp (measurable_const.prodMk measurable_id)))
      (fun p x x' hxx => by rw [hBd p γ γ x x' fun q hq => ⟨rfl, hxx q hq⟩])
    convert this using 1
    funext g p
    simp only [hTdef, mlaw]
    abel
  have hTm : ∀ γ, Measurable (T γ) := fun γ => (hT γ).measurable
  have hT0 : ∀ γ, T γ 0 = γ := by
    intro γ; funext p; simp [hTdef, mlaw, hB0]
  let Γs := {x : ∀ q, α q // ∀ p, x p - τ p x ∈ A p}
  have hcount : Countable Γs := by
    have hinj : Function.Injective (fun x : Γs => fun p => (⟨x.1 p - τ p x.1, x.2 p⟩ : A p)) := by
      intro x y hxy
      apply Subtype.ext
      funext p
      suffices H : ∀ n, ∀ p, h p < n → x.1 p = y.1 p from H (h p + 1) p (by omega)
      intro n
      induction n with
      | zero => intro p hp; omega
      | succ k ih =>
        intro p hp
        have hl : ∀ q, h q < h p → x.1 q = y.1 q := fun q hq => ih q (by omega)
        have e := congrArg Subtype.val (congrFun hxy p)
        simp only at e
        rw [hτ p x.1 y.1 hl] at e
        simpa using e
    exact hinj.countable
  choose inv hinvA hinvT using hinv
  let iv : Γs → Γs := fun γ => ⟨inv γ.1 γ.2, hinvA γ.1 γ.2⟩
  have hiv1 : ∀ (γ : Γs) g, T (iv γ).1 (T γ.1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).1
  have hiv2 : ∀ (γ : Γs) g, T γ.1 (T (iv γ).1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).2
  have hivv : ∀ γ : Γs, iv (iv γ) = γ := by
    intro γ
    apply Subtype.ext
    have e : ∀ g, T (iv (iv γ)).1 g = T γ.1 g := by
      intro g
      calc T (iv (iv γ)).1 g = T (iv (iv γ)).1 (T (iv γ).1 (T γ.1 g)) := by rw [hiv1 γ g]
        _ = T γ.1 g := hiv1 (iv γ) (T γ.1 g)
    rw [← hT0 (iv (iv γ)).1, ← hT0 γ.1, e]
  let ivE : Γs ≃ Γs := ⟨iv, iv, hivv, hivv⟩
  let R : Set (∀ p, α p) := Set.pi Set.univ F
  have hR : MeasurableSet R := MeasurableSet.univ_pi hF
  have hRd := box_fundT h B hBd τ hτ A F hFd
  have hK1 : Measure.pi μ K = ∑' γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) := by
    have hU : K = ⋃ γ : Γs, K ∩ T γ.1 ⁻¹' R := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγF⟩, -⟩ := hRd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, fun p _ => hγF p⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hK.inter (hTm γ.1 hR)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hRd g).unique ⟨γ.2, fun p => hg1 p (Set.mem_univ p)⟩ ⟨δ.2, fun p => hg2 p (Set.mem_univ p)⟩
  have hR1 : Measure.pi μ R = ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) := by
    have hU : R = ⋃ γ : Γs, R ∩ T γ.1 ⁻¹' K := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγK⟩, -⟩ := hKd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, hγK⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hR.inter (hTm γ.1 hK)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hKd g).unique ⟨γ.2, hg1⟩ ⟨δ.2, hg2⟩
  have hterm : ∀ γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) = Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K) := by
    intro γ
    have e : K ∩ T γ.1 ⁻¹' R = T γ.1 ⁻¹' (R ∩ T (iv γ).1 ⁻¹' K) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      rw [hiv1 γ g]
      tauto
    rw [e]
    exact (hT γ.1).measure_preimage (hR.inter (hTm _ hK)).nullMeasurableSet
  rw [hK1, tsum_congr hterm, show (∑' γ : Γs, Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K)) =
      ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) from ivE.tsum_eq (fun γ => Measure.pi μ (R ∩ T γ.1 ⁻¹' K)),
    ← hR1]
  exact Measure.pi_pi μ F
end Formalism.L2.SG.NGCut.SplitEmbedding
