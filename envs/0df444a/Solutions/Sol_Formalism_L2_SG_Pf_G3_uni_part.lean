-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.uni_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:25.503605+00:00
-- url     : https://prove2.me/submissions/4715b6d7-791d-4d48-950f-c5b24923a70b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SdBasisBot
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_UniPart
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_L2_SG_Pf_G3_sd_basis
import Theorems.Thm_Formalism_L2_SG_Pf_G3_sup_cutW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


section
open Module
noncomputable section
namespace Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
private theorem mem_iff_lemma {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl
private theorem smul_mem_lemma_2 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] {g : ι → V} {a : K} (ha : a ∈ S)
    {v : V} (hv : v ∈ spanS S g) : a • v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv ⊢
  obtain ⟨d, hd, rfl⟩ := hv
  exact ⟨fun i => a * d i, fun i => S.mul_mem ha (hd i), by simp [Finset.smul_sum, mul_smul]⟩
private theorem spanS_le_lemma_3 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V}
    {g : ι → V} (hfg : ∀ k, f k ∈ spanS S g) {v : V} (hv : v ∈ spanS S f) : v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  exact AddSubgroup.sum_mem _ fun k _ => smul_mem_lemma_2 (hc k) (hfg k)
private theorem mem_span_lemma_4 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] {g : ι → V} {v : V}
    (hv : v ∈ spanS S g) : v ∈ Submodule.span K (Set.range g) := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, -, rfl⟩ := hv
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
private theorem spans_eq_lemma_5 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V}
    {g : ι → V} (h1 : ∀ k, f k ∈ spanS S g) (h2 : ∀ i, g i ∈ spanS S f) :
    Submodule.span K (Set.range f) = Submodule.span K (Set.range g) ∧
      ∀ v, v ∈ spanS S f ↔ v ∈ spanS S g := by
  refine ⟨le_antisymm ?_ ?_, fun v => ⟨spanS_le_lemma_3 h1, spanS_le_lemma_3 h2⟩⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact mem_span_lemma_4 (h1 k)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_span_lemma_4 (h2 i)
private theorem linInd_lemma_6 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} {f : ι → V} (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0)
    (hn : ∀ i, h (f i) (f i) ≠ 0) : LinearIndependent K f := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 := congrArg (h (f i)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro h'
    exact absurd hi h'
private theorem form_sum_lemma_7 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} [Fintype ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (a c : ι → K) :
    h (∑ i, a i • b i) (∑ j, c j • b j) = ∑ i, star (a i) * c i * h (b i) (b i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  · intro j _ hji
    rw [map_smulₛₗ, LinearMap.smul_apply, ho j i hji, smul_zero]
  · intro h'
    exact absurd (Finset.mem_univ i) h'
private theorem mem_self_lemma_9 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]
private theorem isSD_lemma_8 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {S : Subring K} (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} [Fintype ι]
    [DecidableEq ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i))) :
    IsSD S h (Submodule.span K (Set.range b)) (spanS S b) where
  le := fun m hm => mem_span_lemma_4 hm
  smul_mem := fun a ha m hm => smul_mem_lemma_2 ha hm
  int := by
    intro x hx y hy
    rw [mem_iff_lemma] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    rw [form_sum_lemma_7 ho]
    exact sum_mem fun i _ => S.mul_mem (S.mul_mem (hS.star_mem _ (ha i)) (hc i)) (hu i).2.1
  span := by
    intro x hx
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    choose T hTS hT0 hTg using fun i => hS.frac (g i)
    refine ⟨∏ i, T i, Finset.prod_ne_zero_iff.2 fun i _ => hT0 i, ?_⟩
    rw [mem_iff_lemma]
    refine ⟨fun i => (∏ j, T j) * g i, fun i => ?_, ?_⟩
    · dsimp only
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
      exact S.mul_mem (S.prod_mem fun j _ => hTS j) (hTg i)
    · rw [Finset.smul_sum]
      simp only [smul_smul]
  dual := by
    intro x hx hdual
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    rw [mem_iff_lemma]
    refine ⟨g, fun i => ?_, rfl⟩
    have h1 := hdual (b i) (mem_self_lemma_9 b i)
    rw [map_sum, Finset.sum_eq_single i] at h1
    · rw [map_smul, smul_eq_mul] at h1
      have h2 := S.mul_mem h1 (hu i).2.2
      rwa [mul_assoc, mul_inv_cancel₀ (hu i).1, mul_one] at h2
    · intro j _ hji
      rw [map_smul, ho i j (Ne.symm hji), smul_zero]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
end Formalism.L2.SG.Pf.G3
end
end

set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    {e : ι → ℕ} {i₀ : ι} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) (x : ι → K) (hx : ∀ i, x i ∈ S)
    (hX : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹)) :
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧ (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
      c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧ (∀ k, e k ≠ e i₀ → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  set Xs := ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i with hXs
  have hπ0 : π ≠ 0 := hπ.ne
  have hp0 : π ^ e i₀ ≠ 0 := pow_ne_zero _ hπ0
  obtain ⟨h', hh'⟩ : ∃ h' : V →ₗ⋆[K] V →ₗ[K] K, ∀ v w, h' v w = (π ^ e i₀)⁻¹ * h v w :=
    ⟨(π ^ e i₀)⁻¹ • h, fun v w => by simp only [LinearMap.smul_apply, smul_eq_mul]⟩
  have hstar : ∀ v w, star (h v w) = h w v := fun v w => by
    rw [← starRingEnd_apply]
    exact hs.eq v w
  have hpstar : star ((π ^ e i₀)⁻¹) = (π ^ e i₀)⁻¹ := by rw [star_inv₀, star_pow, hπ.fix]
  have hs' : h'.IsSymm := LinearMap.IsSymm.mk fun v w => by
    rw [hh', hh', starRingEnd_apply, star_mul, hstar, hpstar, mul_comm]
  have hz : ∀ v w, h' v w = 0 → h v w = 0 := fun v w hvw => by
    rw [hh'] at hvw
    exact (mul_eq_zero.1 hvw).resolve_left (inv_ne_zero hp0)
  have hd' : ∀ v, h' v v = 0 → v = 0 := fun v hv => hd v (hz v v hv)
  have hconv : ∀ v, h' v v = h v v * (π ^ e i₀)⁻¹ := fun v => by rw [hh', mul_comm]
  obtain ⟨bP, hbP⟩ : ∃ bP : {i // e i = e i₀} → V, ∀ p, bP p = b p := ⟨fun p => b p, fun _ => rfl⟩
  have hoP : ∀ p q, p ≠ q → h' (bP p) (bP q) = 0 := fun p q hpq => by
    rw [hh', hbP, hbP, ho _ _ (fun hq => hpq (Subtype.ext hq)), mul_zero]
  have huP : ∀ p, IsUnitIn S (h' (bP p) (bP p)) := fun p => by
    rw [hconv, hbP]
    have := hu p
    rwa [p.2] at this
  have hSD := isSD_lemma_8 hS hoP huP
  have hXeq : Xs = ∑ p : {i // e i = e i₀}, x p • bP p := by
    simp only [hbP]
    exact Finset.sum_subtype _ (fun i => by simp) (fun i => x i • b i)
  have hXL : Xs ∈ spanS S bP := (mem_iff_lemma _ _).2 ⟨fun p => x p, fun p => hx p, hXeq⟩
  have hXu' : IsUnitIn S (h' Xs Xs) := by
    rw [hconv]
    exact hX
  have hXX : h' Xs Xs ≠ 0 := hXu'.1
  have hX0 : Xs ≠ 0 := fun h0 => hXX (by rw [h0, map_zero])
  have hXW : Xs ∈ Submodule.span K (Set.range bP) := mem_span_lemma_4 hXL
  obtain ⟨k, f, hof, huf, hspf, hspanf⟩ := sd_basis hS hπ hs' hd' _
    (cutW h' (Submodule.span K (Set.range bP)) Xs) (cutM h' (spanS S bP) Xs) le_rfl
    (hSD.cut hXL hXu')
  have hinf : K ∙ Xs ⊓ cutW h' (Submodule.span K (Set.range bP)) Xs = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv1
    have hv2' : t • Xs ∈ Submodule.span K (Set.range bP) ⊓ LinearMap.ker (h' Xs) := hv2
    have ht := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv2').2
    rw [map_smul, smul_eq_mul] at ht
    rw [(mul_eq_zero.1 ht).resolve_right hXX, zero_smul]
    exact Submodule.zero_mem _
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ Xs)
    (cutW h' (Submodule.span K (Set.range bP)) Xs)
  rw [sup_cutW hXW hXX, hinf, finrank_bot, finrank_span_singleton hX0, ← hspanf,
    finrank_span_eq_card (linInd_lemma_6 hof (fun j => (huf j).1)),
    finrank_span_eq_card (linInd_lemma_6 hoP (fun p => (huP p).1)), Fintype.card_fin] at e1
  set p₀ : {i // e i = e i₀} := ⟨i₀, rfl⟩ with hp₀
  have hQ : Fintype.card {p : {i // e i = e i₀} // p ≠ p₀} = k := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  let σ := Fintype.equivFinOfCardEq hQ
  obtain ⟨gP, hg0, hgq⟩ : ∃ gP : {i // e i = e i₀} → V, gP p₀ = Xs ∧
      ∀ q : {p : {i // e i = e i₀} // p ≠ p₀}, gP q.1 = f (σ q) :=
    ⟨fun p => if hp : p = p₀ then Xs else f (σ ⟨p, hp⟩), dif_pos rfl, fun q => dif_neg q.2⟩
  obtain ⟨c, hcP, hcn⟩ : ∃ c : ι → V, (∀ p : {i // e i = e i₀}, c p = gP p) ∧
      ∀ i, e i ≠ e i₀ → c i = b i :=
    ⟨fun i => if hi : e i = e i₀ then gP ⟨i, hi⟩ else b i, fun p => dif_pos p.2,
      fun i hi => dif_neg hi⟩
  have hc0 : c i₀ = Xs := (hcP p₀).trans hg0
  have hXf : ∀ j, h Xs (f j) = 0 := fun j => by
    have hm : f j ∈ cutW h' (Submodule.span K (Set.range bP)) Xs := by
      rw [← hspanf]
      exact Submodule.subset_span ⟨j, rfl⟩
    have hm' : f j ∈ Submodule.span K (Set.range bP) ⊓ LinearMap.ker (h' Xs) := hm
    exact hz _ _ (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hm').2)
  have hfX : ∀ j, h (f j) Xs = 0 := fun j => by rw [← hstar, hXf, star_zero]
  have hgo : ∀ p p' : {i // e i = e i₀}, p ≠ p' → h (gP p) (gP p') = 0 := by
    intro p p' hpp
    by_cases hp : p = p₀
    · have hp' : p' ≠ p₀ := fun hq => hpp (hp.trans hq.symm)
      rw [hp, hg0, show gP p' = f (σ ⟨p', hp'⟩) from hgq ⟨p', hp'⟩]
      exact hXf _
    · by_cases hp' : p' = p₀
      · rw [hp', hg0, show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩]
        exact hfX _
      · rw [show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩,
          show gP p' = f (σ ⟨p', hp'⟩) from hgq ⟨p', hp'⟩]
        exact hz _ _ (hof _ _ (fun hq => hpp (congrArg Subtype.val (σ.injective hq))))
  have hfL : ∀ j, f j ∈ spanS S bP := fun j => (mem_cutM.1 ((hspf _).1 (mem_self_lemma_9 f j))).1
  have hgL : ∀ p, gP p ∈ spanS S bP := fun p => by
    by_cases hp : p = p₀
    · rw [hp, hg0]
      exact hXL
    · rw [show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩]
      exact hfL _
  have hperp : ∀ w ∈ Submodule.span K (Set.range bP), ∀ j, e j ≠ e i₀ →
      h w (b j) = 0 ∧ h (b j) w = 0 := by
    intro w hw j hj
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    have hne : ∀ p : {i // e i = e i₀}, (p : ι) ≠ j := fun p hq => hj (hq ▸ p.2)
    constructor
    · rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun p _ => by
        rw [map_smulₛₗ, LinearMap.smul_apply, hbP, ho _ _ (hne p), smul_zero]
    · rw [map_sum]
      exact Finset.sum_eq_zero fun p _ => by
        rw [map_smul, hbP, ho _ _ (hne p).symm, smul_zero]
  have hoc : ∀ i j, i ≠ j → h (c i) (c j) = 0 := by
    intro i j hij
    by_cases hi : e i = e i₀
    · by_cases hj : e j = e i₀
      · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, show c j = gP ⟨j, hj⟩ from hcP ⟨j, hj⟩]
        exact hgo _ _ (fun hq => hij (congrArg Subtype.val hq))
      · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, hcn j hj]
        exact (hperp _ (mem_span_lemma_4 (hgL _)) j hj).1
    · rw [hcn i hi]
      by_cases hj : e j = e i₀
      · rw [show c j = gP ⟨j, hj⟩ from hcP ⟨j, hj⟩]
        exact (hperp _ (mem_span_lemma_4 (hgL _)) i hi).2
      · rw [hcn j hj]
        exact ho i j hij
  have huc : ∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹) := by
    intro i
    by_cases hi : e i = e i₀
    · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, hi, ← hconv]
      by_cases hp : (⟨i, hi⟩ : {i // e i = e i₀}) = p₀
      · rw [hp, hg0]
        exact hXu'
      · rw [show gP ⟨i, hi⟩ = f (σ ⟨⟨i, hi⟩, hp⟩) from hgq ⟨⟨i, hi⟩, hp⟩]
        exact huf _
    · rw [hcn i hi]
      exact hu i
  have h1 : ∀ i, c i ∈ spanS S b := by
    intro i
    by_cases hi : e i = e i₀
    · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩]
      exact spanS_le_lemma_3 (fun p => by rw [hbP]; exact mem_self_lemma_9 b p) (hgL _)
    · rw [hcn i hi]
      exact mem_self_lemma_9 b i
  have hfc : ∀ j, f j ∈ spanS S c := fun j => by
    have hfj : f j = c (σ.symm j).1.1 := by rw [hcP, hgq, Equiv.apply_symm_apply]
    rw [hfj]
    exact mem_self_lemma_9 c _
  have h2 : ∀ i, b i ∈ spanS S c := by
    intro i
    by_cases hi : e i = e i₀
    · have hbi : b i ∈ spanS S bP := by
        have hm := mem_self_lemma_9 (S := S) bP ⟨i, hi⟩
        rwa [hbP] at hm
      have hr := (hspf _).2 (proj_mem hSD.toIsLatIn hXL hXu' hbi)
      have ha : h' Xs (b i) * (h' Xs Xs)⁻¹ ∈ S := S.mul_mem (hSD.int _ hXL _ hbi) hXu'.2.2
      have key : b i = (h' Xs (b i) * (h' Xs Xs)⁻¹) • Xs
          + (b i - (h' Xs (b i) * (h' Xs Xs)⁻¹) • Xs) := by abel
      rw [key]
      refine add_mem (smul_mem_lemma_2 ha ?_) (spanS_le_lemma_3 hfc hr)
      rw [← hc0]
      exact mem_self_lemma_9 c i₀
    · rw [← hcn i hi]
      exact mem_self_lemma_9 c i
  obtain ⟨hspc, hiffc⟩ := spans_eq_lemma_5 h1 h2
  exact ⟨c, hoc, huc, hc0, hcn, hspc, hiffc⟩
end Formalism.L2.SG.Pf.G3
