-- Prove2me | solution 1 for ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/eed856b2-58a9-52b7-9046-cebf1057cb06

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres

set_option autoImplicit false

open Set Filter Topology

namespace NoAtomPush

variable {Y : Type*} [TopologicalSpace Y]

theorem continuous_piece (h : Y → ℂ) (hh : Continuous h) (A : Set Y) [∀ y, Decidable (y ∈ A)] (hA : IsOpen A)
    (hz : ∀ x ∉ A, (∀ᶠ y in 𝓝 x, y ∉ A) ∨ h x = 0) :
    Continuous (fun y => if y ∈ A then h y else 0) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ A
  ·
    have heq : (fun y => if y ∈ A then h y else 0) =ᶠ[𝓝 x] h :=
      Filter.eventuallyEq_of_mem (hA.mem_nhds hx) fun y hy => if_pos hy
    exact (hh.continuousAt.congr heq.symm)
  ·
    have hx0 : (if x ∈ A then h x else 0) = 0 := if_neg hx
    rw [ContinuousAt, hx0]
    have hbound : ∀ᶠ y in 𝓝 x, ‖(if y ∈ A then h y else 0)‖ ≤ ‖h y - h x‖ := by
      rcases hz x hx with hev | h0
      · exact hev.mono fun y hy => by simp [hy]
      · refine Filter.Eventually.of_forall fun y => ?_
        by_cases hy : y ∈ A
        · simp [hy, h0]
        · simp [hy]
    have hlim : Tendsto (fun y => ‖h y - h x‖) (𝓝 x) (𝓝 0) := by
      have : Tendsto (fun y => h y - h x) (𝓝 x) (𝓝 (h x - h x)) := (hh.tendsto x).sub tendsto_const_nhds
      rw [sub_self] at this
      exact tendsto_norm_zero.comp this
    exact squeeze_zero_norm' hbound hlim

end NoAtomPush

open NoAtomPush in
theorem solution
    {ιK ιL : Type} (XK : Set (ιK → ℂ × ℂ)) (hXKc : IsCompact XK) (X : Set (ιL → ℂ × ℂ)) (T : Finset ιK)
    (w' : ιK → ιL)
    (B : ιK → ℂ × ℂ → ℂ × ℂ) (hBc : ∀ v ∈ T, Continuous (B v))
    (hBf : ∀ v ∈ T, ∀ c : ℂ × ℂ, ((B v) ⁻¹' {c}).Finite)
    (bc : C(XK, X))
    (hbc : ∀ (x : XK), ∀ v ∈ T, ((bc x : X) : ιL → ℂ × ℂ) (w' v) = B v ((x : ιK → ℂ × ℂ) v))
    (Λ : C(XK, ℂ) →L[ℂ] ℂ)
    (hΛ : ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ T, (y : ιK → ℂ × ℂ) v ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ g‖ < ε) :
    ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(X, ℂ), (∀ y : X, (∃ v ∈ T, (y : ιL → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ (g.comp bc)‖ < ε := by
  classical
  intro τ ε hε

  have hfin : ∀ v : ιK, ((if v ∈ T then (B v) ⁻¹' {τ v} else ∅ : Set (ℂ × ℂ))).Finite := by
    intro v
    by_cases hv : v ∈ T
    · rw [if_pos hv]; exact hBf v hv (τ v)
    · rw [if_neg hv]; exact Set.finite_empty
  let Fs : ιK → Finset (ℂ × ℂ) := fun v => (hfin v).toFinset
  have hFs : ∀ v ∈ T, ∀ c : ℂ × ℂ, c ∈ Fs v ↔ B v c = τ v := by
    intro v hv c
    simp only [Fs, Set.Finite.mem_toFinset, if_pos hv, Set.mem_preimage, Set.mem_singleton_iff]

  let Sec : Type := ∀ v : T, (Fs v.1 : Set (ℂ × ℂ))
  haveI : Fintype Sec := inferInstance
  set Nsec : ℕ := Fintype.card Sec with hNsec
  set ε' : ℝ := ε / (Nsec + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by positivity)

  let τs : Sec → ιK → ℂ × ℂ := fun s v => if hv : v ∈ T then ((s ⟨v, hv⟩ : (Fs v : Set (ℂ × ℂ))) : ℂ × ℂ) else τ v
  have hUs := fun s : Sec => hΛ (τs s) ε' hε'pos
  choose Us hUs_open hUs_small using hUs

  have hsep : ∀ v : ιK, ∃ V : ℂ × ℂ → Set (ℂ × ℂ),
      (∀ c, c ∈ V c ∧ IsOpen (V c)) ∧ (Fs v : Set (ℂ × ℂ)).PairwiseDisjoint V :=
    fun v => (Fs v).finite_toSet.t2_separation
  choose V hV hVdisj using hsep
  let W : ιK → ℂ × ℂ → Set (ℂ × ℂ) := fun v c =>
    V v c ∩ ⋂ s ∈ (Finset.univ.filter fun s : Sec => ∀ hv : v ∈ T, ((s ⟨v, hv⟩ : (Fs v : Set (ℂ × ℂ))) :
      ℂ × ℂ) = c), Us s v
  have hW_open : ∀ v ∈ T, ∀ c ∈ (Fs v : Set (ℂ × ℂ)), IsOpen (W v c) := by
    intro v hv c hc
    exact (hV v c).2.inter (isOpen_biInter_finset fun s _ => (hUs_open s v hv).1)
  have hW_mem : ∀ v ∈ T, ∀ c ∈ (Fs v : Set (ℂ × ℂ)), c ∈ W v c := by
    intro v hv c hc
    refine ⟨(hV v c).1, Set.mem_iInter₂.mpr fun s hs => ?_⟩
    have hs' := (Finset.mem_filter.mp hs).2 hv
    have := (hUs_open s v hv).2
    simp only [τs, dif_pos hv] at this
    rwa [hs'] at this
  have hW_sub_V : ∀ v c, W v c ⊆ V v c := fun v c => Set.inter_subset_left
  have hW_sub_Us : ∀ v (hv : v ∈ T) (s : Sec), W v ((s ⟨v, hv⟩ : (Fs v : Set (ℂ × ℂ))) : ℂ × ℂ) ⊆ Us s v := by
    intro v hv s x hx
    have hx2 := (Set.mem_iInter₂.mp hx.2) s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hv' => rfl⟩)
    exact hx2

  have hKv : ∀ v : ιK, IsCompact ((fun x : ιK → ℂ × ℂ => x v) '' XK) :=
    fun v => hXKc.image (continuous_apply v)
  have hUv : ∀ v ∈ T, ∃ Uv : Set (ℂ × ℂ), IsOpen Uv ∧ τ v ∈ Uv ∧
      ∀ p ∈ (fun x : ιK → ℂ × ℂ => x v) '' XK, B v p ∈ Uv → ∃ c ∈ (Fs v : Set (ℂ × ℂ)), p ∈ W v c := by
    intro v hv

    set C : Set (ℂ × ℂ) := (fun x : ιK → ℂ × ℂ => x v) '' XK \ ⋃ c ∈ (Fs v : Set (ℂ × ℂ)), W v c with hC
    have hCc : IsCompact C := (hKv v).diff (isOpen_biUnion fun c hc => hW_open v hv c hc)
    have hBC : IsCompact (B v '' C) := hCc.image (hBc v hv)
    have hτC : τ v ∉ B v '' C := by
      rintro ⟨p, hp, hpτ⟩
      have hpF : p ∈ (Fs v : Set (ℂ × ℂ)) := by
        rw [Finset.mem_coe, hFs v hv]; exact hpτ
      exact hp.2 (Set.mem_biUnion hpF (hW_mem v hv p hpF))
    refine ⟨(B v '' C)ᶜ, hBC.isClosed.isOpen_compl, hτC, fun p hp hpU => ?_⟩
    by_contra hno
    push Not at hno
    have hpC : p ∈ C := ⟨hp, fun hmem => by
      obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hmem
      exact hno c hc hpc⟩
    exact hpU ⟨p, hpC, rfl⟩
  choose! Uv hUv_open hUv_mem hUv_pre using hUv

  refine ⟨fun v => if v ∈ T then Uv v else Set.univ, fun v hv => ?_, fun g hg hg1 => ?_⟩
  · simp only [if_pos hv]
    exact ⟨hUv_open v hv, hUv_mem v hv⟩

  set h : C(XK, ℂ) := g.comp bc with hh
  let A : Sec → Set XK := fun s => {x | ∀ v : T, ((x : ιK → ℂ × ℂ) v.1) ∈ W v.1 (s v)}
  have hA_open : ∀ s, IsOpen (A s) := by
    intro s
    have : A s = ⋂ v : T, (fun x : XK => (x : ιK → ℂ × ℂ) v.1) ⁻¹' W v.1 (s v) := by
      ext x; simp [A]
    rw [this]
    exact isOpen_iInter_of_finite fun v =>
      (hW_open v.1 v.2 _ (s v).2).preimage ((continuous_apply v.1).comp continuous_subtype_val)

  have hcover : ∀ x : XK, h x ≠ 0 → ∃ s, x ∈ A s := by
    intro x hx
    have hin : ∀ v ∈ T, ((bc x : X) : ιL → ℂ × ℂ) (w' v) ∈ (if v ∈ T then Uv v else Set.univ) := by
      by_contra hno
      push Not at hno
      obtain ⟨v, hv, hvU⟩ := hno
      exact hx (hg (bc x) ⟨v, hv, hvU⟩)
    have hc : ∀ v : T, ∃ c ∈ (Fs v.1 : Set (ℂ × ℂ)), (x : ιK → ℂ × ℂ) v.1 ∈ W v.1 c := by
      intro v
      have h1 := hin v.1 v.2
      rw [if_pos v.2, hbc x v.1 v.2] at h1
      exact hUv_pre v.1 v.2 _ ⟨x, x.2, rfl⟩ h1
    choose cs hcs hxcs using hc
    exact ⟨fun v => ⟨cs v, hcs v⟩, fun v => hxcs v⟩

  have hdisj : ∀ s s' : Sec, s ≠ s' → ∀ x : XK, x ∈ A s → x ∉ A s' := by
    intro s s' hss' x hxs hxs'
    apply hss'
    funext v
    by_contra hne
    have hne' : ((s v : (Fs v.1 : Set (ℂ × ℂ))) : ℂ × ℂ) ≠ ((s' v : (Fs v.1 : Set (ℂ × ℂ))) : ℂ × ℂ) :=
      fun e => hne (Subtype.ext e)
    have hd := hVdisj v.1 (s v).2 (s' v).2 hne'
    exact Set.disjoint_left.mp hd (hW_sub_V _ _ (hxs v)) (hW_sub_V _ _ (hxs' v))

  have hpiece_cont : ∀ s, Continuous (fun y : XK => if y ∈ A s then h y else 0) := by
    intro s
    refine continuous_piece h h.continuous (A s) (hA_open s) fun x hx => ?_
    by_cases hex : ∃ s', x ∈ A s'
    · obtain ⟨s', hs'⟩ := hex
      have hne : s' ≠ s := fun e => hx (e ▸ hs')
      left
      exact Filter.eventually_of_mem ((hA_open s').mem_nhds hs') fun y hy hyA => hdisj s' s hne y hy hyA
    · right
      by_contra h0
      exact hex (hcover x h0)
  let piece : Sec → C(XK, ℂ) := fun s => ⟨fun y => if y ∈ A s then h y else 0, hpiece_cont s⟩
  have hpiece_apply : ∀ s (y : XK), piece s y = if y ∈ A s then h y else 0 := fun s y => rfl

  have hsum : h = ∑ s, piece s := by
    ext x
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    by_cases hex : ∃ s, x ∈ A s
    · obtain ⟨s, hs⟩ := hex
      rw [Finset.sum_eq_single s (fun s' _ hs' => by rw [hpiece_apply, if_neg (hdisj s s' (Ne.symm hs') x hs)])
        (fun habs => absurd (Finset.mem_univ s) habs), hpiece_apply, if_pos hs]
    · have h0 : h x = 0 := by
        by_contra h0; exact hex (hcover x h0)
      rw [h0, eq_comm]
      exact Finset.sum_eq_zero fun s _ => by rw [hpiece_apply, if_neg (fun hs => hex ⟨s, hs⟩)]

  have hsmall : ∀ s, ‖Λ (piece s)‖ < ε' := by
    intro s
    refine hUs_small s (piece s) (fun y hy => ?_) (fun y => ?_)
    · obtain ⟨v, hv, hyv⟩ := hy
      rw [hpiece_apply, if_neg]
      intro hyA
      exact hyv (hW_sub_Us v hv s (hyA ⟨v, hv⟩))
    · rw [hpiece_apply]
      by_cases hyA : y ∈ A s
      · rw [if_pos hyA, hh, ContinuousMap.comp_apply]; exact hg1 _
      · rw [if_neg hyA, norm_zero]; exact zero_le_one

  calc ‖Λ h‖ = ‖∑ s, Λ (piece s)‖ := by rw [hsum, map_sum]
    _ ≤ ∑ s, ‖Λ (piece s)‖ := norm_sum_le _ _
    _ ≤ ∑ _s : Sec, ε' := Finset.sum_le_sum fun s _ => (hsmall s).le
    _ = Nsec * ε' := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNsec]
    _ < ε := by
        rw [hε', mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

end S_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres
end P2MW
export P2MW.S_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres (solution)
