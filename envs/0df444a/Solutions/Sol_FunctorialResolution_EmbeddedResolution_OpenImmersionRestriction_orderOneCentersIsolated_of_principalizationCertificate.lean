-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.orderOneCentersIsolated_of_principalizationCertificate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:03.400341+00:00
-- url     : https://prove2.me/submissions/9ada24c6-132d-4d76-971c-d1fed10734f4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_mem_support_iff_of_agreeNear
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isClosed_preimage_subscheme__comp___f5c54755774e
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_false_of_isOpen_preimage_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_add_orderAt_le_orderAt_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isGenericPoint_preimage_of_isInducing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_iff_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap_eq
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
private theorem orderOneCentersIsolated_of_support_subset {V : VanishingAssignment.{u}} {k : Type u} [Field k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (I : W.IdealSheafData) (m : ℕ)
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : (Z.support : Set ↥W) ⊆ Mem) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro C _ hS1 _ hxi1M _ _ _ _
  exact hxi1M (h (hS1 C.generic1.mem))
private theorem orderOneCentersIsolated_of_two_le {V : VanishingAssignment.{u}} {k : Type u} [Field k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (I : W.IdealSheafData) (m : ℕ)
    {Mem : Set ↥W} {Z : W.IdealSheafData} (hm : 2 ≤ m) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro _ hm1 _ _ _ _ _ _ _
  omega
private theorem orderOneCentersIsolated_of_eq_mul_of_subset_orderAtLeastLocus {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
    (ih : OrderOneCentersIsolated V W p N μ Mem Z) : OrderOneCentersIsolated V W p I m Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2I
  have hxi1S : C.xi1 ∈ C.S1 := C.generic1.mem
  have hM1 : C.xi1 ∉ (M.support : Set ↥W) := fun hh => hxi1M (hM hh)
  have hM2 : C.xi2 ∉ (M.support : Set ↥W) := fun hh => hxi2M (hM hh)
  obtain ⟨Uc, hUcmem, hUctop⟩ : ∃ Uc : W.Opens, C.xi1 ∈ Uc ∧ M.comap Uc.ι = ⊤ :=
    ⟨⟨(M.support : Set ↥W)ᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hM1,
      comap_ι_eq_top_of_disjoint M _ disjoint_compl_left⟩
  have hAIN : AgreeNear I N C.xi1 :=
    ⟨Uc, hUcmem, by rw [hI, hV.comap_mul, hUctop, hV.top_mul]⟩
  have hAN : AgreeNear N (V W ⟨C.S1, C.closed1⟩) C.xi1 :=
    hV.agreeNear_trans W N I (V W ⟨C.S1, C.closed1⟩) C.xi1 (agreeNear_symm hAIN) hagree
  have hM0 : orderAt M C.xi1 = 0 := (orderAt_eq_zero_iff_not_mem_support M C.xi1).2 hM1
  have hle : orderAt N C.xi1 ≤ 1 := by
    have h2 := add_orderAt_le_orderAt_mul M N C.xi1
    rw [hM0, zero_add, ← hI, hord] at h2
    exact h2
  have hmu1 : (μ : ℕ∞) ≤ orderAt N C.xi1 := (mem_orderAtLeastLocus_iff N μ C.xi1).1 (hZ (hS1 hxi1S))
  have hμle : μ ≤ 1 := by exact_mod_cast le_trans hmu1 hle
  have hμ1 : μ = 1 := by omega
  have hordN : orderAt N C.xi1 = 1 := by
    refine le_antisymm hle ?_
    rw [hμ1] at hmu1
    exact_mod_cast hmu1
  have hxi2Nmem : C.xi2 ∈ (N.support : Set ↥W) := by
    rw [hI, hV.support_mul] at hxi2I
    rcases (Set.mem_union _ _ _).1 hxi2I with h' | h'
    · exact absurd h' hM2
    · exact h'
  exact ih C hμ1 hS1 hxi2Z hxi1M hxi2M hAN hordN hxi2Nmem
private theorem false_of_orderOneCentersIsolated_comap_opens {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U₀ : W.Opens) (C : IrreducibleClosedPair W) (hptU : C.pt ∈ (U₀ : Set ↥W))
    (key : OrderOneCentersIsolated V U₀.toScheme (U₀.ι ≫ p) (I.comap U₀.ι) m (⇑U₀.ι.base ⁻¹' Mem)
      (Z.comap U₀.ι))
    (hm1 : m = 1) (hS1 : C.S1 ⊆ (Z.support : Set ↥W)) (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi1M : C.xi1 ∉ Mem) (hxi2M : C.xi2 ∉ Mem)
    (hagree : AgreeNear I (V W ⟨C.S1, C.closed1⟩) C.xi1) (hord : orderAt I C.xi1 = 1)
    (hxi2I : C.xi2 ∈ (I.support : Set ↥W)) : False := by
  have hopenU : IsOpen ((U₀ : Set ↥W)) := hV.isOpen_opens W U₀
  have hxi1U : C.xi1 ∈ (U₀ : Set ↥W) :=
    (C.generic1.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_first_closed, hptU⟩
  have hxi2U : C.xi2 ∈ (U₀ : Set ↥W) :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hrange : Set.range ⇑U₀.ι.base = (U₀ : Set ↥W) := hV.range_ι W U₀
  obtain ⟨x1, hx1⟩ : ∃ y, U₀.ι.base y = C.xi1 := by
    rw [← Set.mem_range, hrange]; exact hxi1U
  obtain ⟨x2, hx2⟩ : ∃ y, U₀.ι.base y = C.xi2 := by
    rw [← Set.mem_range, hrange]; exact hxi2U
  obtain ⟨x0, hx0⟩ : ∃ y, U₀.ι.base y = C.pt := by
    rw [← Set.mem_range, hrange]; exact hptU
  have hcont : Continuous ⇑U₀.ι.base := (hV.isEmbedding_ι W U₀).continuous
  have hg1 : IsGenericPoint x1 (⇑U₀.ι.base ⁻¹' C.S1) :=
    isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U₀).toIsInducing C.generic1 hx1
  have hg2 : IsGenericPoint x2 (⇑U₀.ι.base ⁻¹' C.S2) :=
    isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U₀).toIsInducing C.generic2 hx2
  refine key
    { S1 := ⇑U₀.ι.base ⁻¹' C.S1
      S2 := ⇑U₀.ι.base ⁻¹' C.S2
      xi1 := x1
      xi2 := x2
      pt := x0
      closed1 := C.closed1.preimage hcont
      closed2 := C.closed2.preimage hcont
      irred1 := by
        rw [← hg1.def]
        exact isIrreducible_singleton.closure
      irred2 := by
        rw [← hg2.def]
        exact isIrreducible_singleton.closure
      generic1 := hg1
      generic2 := hg2
      mem_first_closed := by
        show U₀.ι.base x0 ∈ C.S1
        rw [hx0]; exact C.mem_first_closed
      mem_second_closed := by
        show U₀.ι.base x0 ∈ C.S2
        rw [hx0]; exact C.mem_second_closed }
    hm1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [support_comap_eq]
    exact Set.preimage_mono hS1
  · rw [support_comap_eq]
    intro hcon
    apply hxi2Z
    have h' : U₀.ι.base x2 ∈ (Z.support : Set ↥W) := hcon
    rwa [hx2] at h'
  · intro hcon
    apply hxi1M
    have h' : U₀.ι.base x1 ∈ Mem := hcon
    rwa [hx1] at h'
  · intro hcon
    apply hxi2M
    have h' : U₀.ι.base x2 ∈ Mem := hcon
    rwa [hx2] at h'
  · have h1 : AgreeNear I (V W ⟨C.S1, C.closed1⟩) (U₀.ι.base x1) := by
      rw [hx1]; exact hagree
    have h2 := hV.agreeNear_comap W U₀ I (V W ⟨C.S1, C.closed1⟩) x1 h1
    rw [hV.comap_vanishing W ⟨C.S1, C.closed1⟩ U₀
      ⟨⇑U₀.ι.base ⁻¹' C.S1, C.closed1.preimage hcont⟩ rfl] at h2
    exact h2
  · show orderAt (I.comap U₀.ι) x1 = 1
    rw [hV.orderAt_comap W U₀ I x1, hx1]
    exact hord
  · show x2 ∈ ((I.comap U₀.ι).support : Set ↥(U₀.toScheme))
    rw [support_comap_eq]
    show U₀.ι.base x2 ∈ (I.support : Set ↥W)
    rw [hx2]
    exact hxi2I
private theorem orderOneCentersIsolated_of_forall_opens {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      OrderOneCentersIsolated V (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2I
  have hz : C.pt ∈ Z.support := hS1 C.mem_first_closed
  exact false_of_orderOneCentersIsolated_comap_opens hV (U C.pt hz) C (hU C.pt hz) (ih C.pt hz) hm1 hS1 hxi2Z
    hxi1M hxi2M hagree hord hxi2I
private theorem false_of_isSmoothDivisor_of_orderOneCentersIsolated {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (C : IrreducibleClosedPair W) (U₀ : W.Opens) (H₀ : (U₀.toScheme).IdealSheafData)
    (Jz : (H₀.subscheme).IdealSheafData)
    (hptU : C.pt ∈ (U₀ : Set ↥W))
    (hH : IsSmoothDivisor (U₀.ι ≫ p) H₀)
    (hNsubH : ((N.comap U₀.ι).support : Set ↥(U₀.toScheme)) ⊆
      (H₀.support : Set ↥(U₀.toScheme)))
    (hZH : ((Z.comap U₀.ι).support : Set ↥(U₀.toScheme)) ⊆
      (H₀.support : Set ↥(U₀.toScheme)))
    (hcomp : NonzeroOnComponents Jz)
    (hloc : ∀ x : ↥(H₀.subscheme), (H₀.subschemeι ≫ U₀.ι).base x ∉ Mem →
      ∃ V' : (H₀.subscheme).Opens, x ∈ V' ∧
        Jz.comap V'.ι = ((N.comap U₀.ι).comap H₀.subschemeι).comap V'.ι)
    (key : OrderOneCentersIsolated V H₀.subscheme (H₀.subschemeι ≫ (U₀.ι ≫ p)) Jz μ
      (⇑(H₀.subschemeι ≫ U₀.ι).base ⁻¹' Mem) ((Z.comap U₀.ι).comap H₀.subschemeι))
    (hm1 : μ = 1) (hS1 : C.S1 ⊆ (Z.support : Set ↥W)) (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi1M : C.xi1 ∉ Mem) (hxi2M : C.xi2 ∉ Mem)
    (hagree : AgreeNear N (V W ⟨C.S1, C.closed1⟩) C.xi1) (_hord : orderAt N C.xi1 = 1)
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by
  have hptZ : C.pt ∈ (Z.support : Set ↥W) := hS1 C.mem_first_closed
  have hopenU : IsOpen ((U₀ : Set ↥W)) := hV.isOpen_opens W U₀
  have hxi1U : C.xi1 ∈ (U₀ : Set ↥W) :=
    (C.generic1.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_first_closed, hptU⟩
  have hxi2U : C.xi2 ∈ (U₀ : Set ↥W) :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hZsub : ⇑U₀.ι.base ⁻¹' (Z.support : Set ↥W) ⊆ (H₀.support : Set ↥(U₀.toScheme)) := by
    rw [← support_comap_eq]
    exact hZH
  have hNsub : ⇑U₀.ι.base ⁻¹' (N.support : Set ↥W) ⊆ (H₀.support : Set ↥(U₀.toScheme)) := by
    rw [← support_comap_eq]
    exact hNsubH
  obtain ⟨y1, hy1⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U₀ H₀ (Z.support : Set ↥W) hZsub C.xi1 hxi1U
    (hS1 C.generic1.mem)
  obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U₀ H₀ (Z.support : Set ↥W) hZsub C.pt hptU hptZ
  obtain ⟨y2, hy2⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U₀ H₀ (N.support : Set ↥W) hNsub C.xi2 hxi2U
    hxi2N
  have hgen1 : IsGenericPoint y1 ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1) :=
    isGenericPoint_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S1 C.xi1 C.generic1 y1 hy1
  have hgen2 : IsGenericPoint y2 ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S2) :=
    isGenericPoint_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S2 C.xi2 C.generic2 y2 hy2
  have hcl1 : IsClosed ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1) :=
    isClosed_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S1 C.closed1
  have hcl2 : IsClosed ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S2) :=
    isClosed_preimage_subschemeι_comp_ι hV W U₀ H₀ C.S2 C.closed2
  have hA1 : AgreeNear Jz ((N.comap U₀.ι).comap H₀.subschemeι) y1 := by
    refine hloc y1 ?_
    rw [hy1]
    exact hxi1M
  have hA2 : AgreeNear ((N.comap U₀.ι).comap H₀.subschemeι)
      (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 := by
    refine hV.agreeNear_vanishing_restrict W N U₀ H₀ ⟨C.S1, C.closed1⟩
      ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩ y1 rfl ?_ ?_
    · exact fun a ha => hZsub (Set.preimage_mono hS1 ha)
    · rw [hy1]
      exact hagree
  have hA3 : AgreeNear Jz (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 :=
    hV.agreeNear_trans H₀.subscheme Jz ((N.comap U₀.ι).comap H₀.subschemeι)
      (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 hA1 hA2
  have hy1mem : y1 ∈ (Jz.support : Set ↥(H₀.subscheme)) := by
    refine (mem_support_iff_of_agreeNear hV hA3).2 ?_
    rw [hV.support_vanishing]
    exact hgen1.mem
  have hnotcomp : ((H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1) ∉
      irreducibleComponents ↥(H₀.subscheme) := by
    intro hmem
    refine hV.not_subset_support_of_nonzeroOnComponents H₀.subscheme Jz hcomp _ hmem ?_
    rw [← hgen1.def]
    exact (hV.isClosed_support H₀.subscheme Jz).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hy1mem)
  have hordV : orderAt (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 = 1 :=
    hV.orderAt_vanishing_eq_one k W p U₀ H₀ hH
      ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩ y1 hgen1 hnotcomp
  have hordJ : orderAt Jz y1 = 1 := by
    rw [hV.orderAt_congr H₀.subscheme Jz
      (V H₀.subscheme ⟨(H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1, hcl1⟩) y1 hA3]
    exact hordV
  have hA2' : AgreeNear Jz ((N.comap U₀.ι).comap H₀.subschemeι) y2 := by
    refine hloc y2 ?_
    rw [hy2]
    exact hxi2M
  have hy2mem : y2 ∈ (Jz.support : Set ↥(H₀.subscheme)) := by
    refine (mem_support_iff_of_agreeNear hV hA2').2 ?_
    rw [support_comap_eq, support_comap_eq]
    show U₀.ι.base (H₀.subschemeι.base y2) ∈ (N.support : Set ↥W)
    rw [← hV.base_comp _ _ _ H₀.subschemeι U₀.ι y2, hy2]
    exact hxi2N
  refine key
    { S1 := (H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S1
      S2 := (H₀.subschemeι ≫ U₀.ι).base ⁻¹' C.S2
      xi1 := y1
      xi2 := y2
      pt := y0
      closed1 := hcl1
      closed2 := hcl2
      irred1 := by
        rw [← hgen1.def]
        exact isIrreducible_singleton.closure
      irred2 := by
        rw [← hgen2.def]
        exact isIrreducible_singleton.closure
      generic1 := hgen1
      generic2 := hgen2
      mem_first_closed := by
        show (H₀.subschemeι ≫ U₀.ι).base y0 ∈ C.S1
        rw [hy0]; exact C.mem_first_closed
      mem_second_closed := by
        show (H₀.subschemeι ≫ U₀.ι).base y0 ∈ C.S2
        rw [hy0]; exact C.mem_second_closed }
    hm1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [support_comap_eq, support_comap_eq]
    intro a ha
    show U₀.ι.base (H₀.subschemeι.base a) ∈ (Z.support : Set ↥W)
    rw [← hV.base_comp _ _ _ H₀.subschemeι U₀.ι a]
    exact hS1 ha
  · rw [support_comap_eq, support_comap_eq]
    intro hcon
    apply hxi2Z
    have h' : U₀.ι.base (H₀.subschemeι.base y2) ∈ (Z.support : Set ↥W) := hcon
    rw [← hV.base_comp _ _ _ H₀.subschemeι U₀.ι y2, hy2] at h'
    exact h'
  · intro hcon
    apply hxi1M
    have h' : (H₀.subschemeι ≫ U₀.ι).base y1 ∈ Mem := hcon
    rwa [hy1] at h'
  · intro hcon
    apply hxi2M
    have h' : (H₀.subschemeι ≫ U₀.ι).base y2 ∈ Mem := hcon
    rwa [hy2] at h'
  · exact hA3
  · exact hordJ
  · exact hy2mem
private theorem orderOneCentersIsolated_of_isSmoothDivisor {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), ((U z hz).toScheme).IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((N.comap (U z hz).ι).support : Set ↥((U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥((U z hz).toScheme)))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((Z.comap (U z hz).ι).support : Set ↥((U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥((U z hz).toScheme)))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (((H z hz)).subscheme).IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        ((Z.comap (U z hz).ι).support : Set ↥((U z hz).toScheme))))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : ((H z hz).subscheme).IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : ((H z hz).subscheme).IdealSheafData),
      J z hz = some Jz → ∀ x : ↥((H z hz).subscheme),
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V' : ((H z hz).subscheme).Opens, x ∈ V' ∧
          Jz.comap V'.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V'.ι)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : ((H z hz).subscheme).IdealSheafData),
      J z hz = some Jz →
      OrderOneCentersIsolated V ((H z hz).subscheme) ((H z hz).subschemeι ≫ ((U z hz).ι ≫ p)) Jz μ
        (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    OrderOneCentersIsolated V W p N μ Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2N
  have hz : C.pt ∈ Z.support := hS1 C.mem_first_closed
  have hptZ : C.pt ∈ (Z.support : Set ↥W) := hS1 C.mem_first_closed
  rcases hJJ : J C.pt hz with _ | Jz
  · exact false_of_isOpen_preimage_support hV W N Z C (U C.pt hz) (H C.pt hz) (hU C.pt hz) hptZ
      (hZH C.pt hz) (hNsubH C.pt hz) (hJnone C.pt hz hJJ) hxi2Z hxi2N
  · exact false_of_isSmoothDivisor_of_orderOneCentersIsolated hV C (U C.pt hz) (H C.pt hz) Jz (hU C.pt hz) (hH C.pt hz)
      (hNsubH C.pt hz) (hZH C.pt hz) (hJcomp C.pt hz Jz hJJ) (hJloc C.pt hz Jz hJJ)
      (ih C.pt hz Jz hJJ) hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2N
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
    (h : PrincipalizationCertificate W p I m Mem Z) : OrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W' p' I' m' Mem' Z' _ => OrderOneCentersIsolated V W' p' I' m' Mem' Z')
    (motive_2 := fun W' p' N' μ' Mem' Z' _ => OrderOneCentersIsolated V W' p' N' μ' Mem' Z')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W' p' I' m' Mem' Z' hmem
    exact orderOneCentersIsolated_of_support_subset I' m' hmem
  · intro W' p' I' m' Mem' Z' hm
    exact orderOneCentersIsolated_of_two_le I' m' hm
  · intro W' p' I' m' Mem' Z' M' N' μ' hI' hM' hmu' hZ' hcert' ihc
    exact orderOneCentersIsolated_of_eq_mul_of_subset_orderAtLeastLocus hV M' N' μ' hI' hM' hmu' hZ' ihc
  · intro W' p' I' m' Mem' Z' U' hU' hcert' ihc
    exact orderOneCentersIsolated_of_forall_opens hV U' hU' ihc
  · intro W' p' N' μ' Mem' Z' hmem
    exact orderOneCentersIsolated_of_support_subset N' μ' hmem
  · intro W' p' N' μ' Mem' Z' hmu
    exact orderOneCentersIsolated_of_two_le N' μ' hmu
  · intro W' p' N' μ' Mem' Z' U' hU' hcert' ihc
    exact orderOneCentersIsolated_of_forall_opens hV U' hU' ihc
  · intro W' p' N' μ' Mem' Z' U' hU' H' hH' hNH' hZH' J' hJnone' hJcomp' hJloc' hJcert' ihc
    exact orderOneCentersIsolated_of_isSmoothDivisor hV U' hU' H' hH' hNH' hZH' J' hJnone' hJcomp' hJloc' ihc
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
