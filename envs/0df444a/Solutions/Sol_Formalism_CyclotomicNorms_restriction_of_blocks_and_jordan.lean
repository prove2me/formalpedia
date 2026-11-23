-- Prove2me | solution 1 for Formalism.CyclotomicNorms.restriction_of_blocks_and_jordan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:52.786252+00:00
-- url     : https://prove2.me/submissions/c1eafcb0-a778-450e-bd80-2e2800219319

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
import Theorems.Thm_Formalism_CyclotomicNorms_eigen_mem_span
import Theorems.Thm_Formalism_CyclotomicNorms_mem_of_repr_ne_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_power_of_p_cycle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms
namespace Formalism.CyclotomicNorms
theorem _root_.solution (hB : BlocksCycle) (hJ : JordanTransitive) : Restriction := by
  intro G k V _ _ _ _ ρ N H _ I e χ φ π p hN8 hfin hsolv hIH hirr he hsep hφI hπ hp hcard hp3 hpc
    W₀ hW₀
  classical
  by_cases hne : W₀ = ⊥
  · exact Or.inl hne
  right
  obtain ⟨idx, hidx⟩ : ∃ f : Submodule k V → Finset (Fin N), ∀ U i, i ∈ f U ↔ e i ∈ U :=
    ⟨fun U => Finset.univ.filter (fun i => e i ∈ U), fun U i => by simp⟩
  have hinj : ∀ g : G, Function.Injective (ρ g) := by
    intro g a b hab
    have h1 : ∀ x, ρ g⁻¹ (ρ g x) = x := fun x => by
      calc ρ g⁻¹ (ρ g x) = ρ (g⁻¹ * g) x := by rw [map_mul ρ g⁻¹ g, Module.End.mul_apply]
        _ = x := by rw [inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 a, ← h1 b, hab]
  have hI : ∀ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) →
      ∀ w ∈ U, ∀ i, e.repr w i ≠ 0 → e i ∈ U := fun U hU =>
    mem_of_repr_ne_zero ρ e χ I he hsep U (fun y hy x hx => hU y (hIH hy) x hx)
  have hspan : ∀ U : Submodule k V, ∀ x : V, (∀ i, e.repr x i ≠ 0 → e i ∈ U) → x ∈ U := by
    intro U x hx
    rw [← e.sum_repr x]
    refine U.sum_mem fun i _ => ?_
    by_cases h0 : e.repr x i = 0
    · rw [h0, zero_smul]
      exact U.zero_mem
    · exact U.smul_mem _ (hx i h0)
  have htr : ∀ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) → ∀ g : G,
      ∀ h ∈ H, ∀ x ∈ U.map (ρ g), ρ h x ∈ U.map (ρ g) := by
    intro U hU g h hh x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have hc : g⁻¹ * h * g ∈ H := by
      simpa using (inferInstance : H.Normal).conj_mem h hh g⁻¹
    refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * h * g) y, hU _ hc y hy, ?_⟩
    calc ρ g (ρ (g⁻¹ * h * g) y) = ρ (g * (g⁻¹ * h * g)) y := by
          rw [map_mul ρ g (g⁻¹ * h * g), Module.End.mul_apply]
      _ = ρ (h * g) y := by rw [show g * (g⁻¹ * h * g) = h * g by group]
      _ = ρ h (ρ g y) := by rw [map_mul ρ h g, Module.End.mul_apply]
  have hsing : ∀ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) → ∀ j, idx U = {j} →
      ∀ x ∈ U, x = e.repr x j • e j := by
    intro U hU j hj x hx
    conv_lhs => rw [← e.sum_repr x]
    refine Finset.sum_eq_single j (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ j) h)
    by_contra hne
    have h1 := (hidx U l).mpr (hI U hU x hx l (fun h0 => hne (by rw [h0, zero_smul])))
    rw [hj, Finset.mem_singleton] at h1
    exact hl h1
  have hfinr : ∀ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) →
      Module.finrank k U = (idx U).card := by
    intro U hU
    have hli : LinearIndependent k (fun i : (idx U) => e i) :=
      e.linearIndependent.comp (fun i : (idx U) => (i : Fin N)) Subtype.val_injective
    have heq : U = Submodule.span k (Set.range fun i : (idx U) => e i) := by
      apply le_antisymm
      · intro x hx
        apply hspan
        intro i hi
        exact Submodule.subset_span ⟨⟨i, (hidx U i).mpr (hI U hU x hx i hi)⟩, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (hidx U i).mp i.2
    have h2 := finrank_span_eq_card hli
    rw [← heq] at h2
    rw [h2, Fintype.card_coe]
  have hcardtr : ∀ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) → ∀ g : G,
      (idx (U.map (ρ g))).card = (idx U).card := by
    intro U hU g
    rw [← hfinr _ (htr U hU g), ← hfinr U hU]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ρ g) (hinj g) U)).symm
  have hex : ∃ n, ∃ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) ∧ U ≠ ⊥ ∧
      (idx U).card = n := ⟨_, W₀, hW₀, hne, rfl⟩
  obtain ⟨W, hW, hWne, hWm⟩ := Nat.find_spec hex
  have hmin : ∀ U : Submodule k V, (∀ h ∈ H, ∀ x ∈ U, ρ h x ∈ U) → U ≠ ⊥ →
      (idx W).card ≤ (idx U).card := by
    intro U hU hU0
    rw [hWm]
    exact Nat.find_min' hex ⟨U, hU, hU0, rfl⟩
  have hmap1 : W.map (ρ 1) = W := by rw [map_one, Module.End.one_eq_id, Submodule.map_id]
  have hFeq : ∀ g₁ g₂ : G, ∀ j, e j ∈ W.map (ρ g₁) → e j ∈ W.map (ρ g₂) →
      idx (W.map (ρ g₁)) = idx (W.map (ρ g₂)) := by
    intro g₁ g₂ j h1 h2
    have hX : ∀ h ∈ H, ∀ x ∈ W.map (ρ g₁) ⊓ W.map (ρ g₂), ρ h x ∈ W.map (ρ g₁) ⊓ W.map (ρ g₂) :=
      fun h hh x hx => Submodule.mem_inf.mpr ⟨htr W hW g₁ h hh x (Submodule.mem_inf.mp hx).1,
        htr W hW g₂ h hh x (Submodule.mem_inf.mp hx).2⟩
    have hX0 : W.map (ρ g₁) ⊓ W.map (ρ g₂) ≠ ⊥ := by
      intro h0
      apply e.ne_zero j
      have h3 : e j ∈ W.map (ρ g₁) ⊓ W.map (ρ g₂) := Submodule.mem_inf.mpr ⟨h1, h2⟩
      rwa [h0, Submodule.mem_bot] at h3
    have hm := hmin _ hX hX0
    have hs1 : idx (W.map (ρ g₁) ⊓ W.map (ρ g₂)) ⊆ idx (W.map (ρ g₁)) := fun i hi =>
      (hidx _ i).mpr (Submodule.mem_inf.mp ((hidx _ i).mp hi)).1
    have hs2 : idx (W.map (ρ g₁) ⊓ W.map (ρ g₂)) ⊆ idx (W.map (ρ g₂)) := fun i hi =>
      (hidx _ i).mpr (Submodule.mem_inf.mp ((hidx _ i).mp hi)).2
    rw [← Finset.eq_of_subset_of_card_le hs1 (by rw [hcardtr W hW g₁]; exact hm),
      ← Finset.eq_of_subset_of_card_le hs2 (by rw [hcardtr W hW g₂]; exact hm)]
  obtain ⟨Y, hY⟩ : ∃ Y : Submodule k V, ∀ x, x ∈ Y ↔
      ∀ j, (∀ g, e j ∉ W.map (ρ g)) → e.repr x j = 0 :=
    ⟨{ carrier := {x | ∀ j, (∀ g, e j ∉ W.map (ρ g)) → e.repr x j = 0}
       add_mem' := fun {a b} ha hb j hj => by
         rw [map_add, Finsupp.add_apply, ha j hj, hb j hj, add_zero]
       zero_mem' := fun j _ => by rw [map_zero, Finsupp.zero_apply]
       smul_mem' := fun c {x} hx j hj => by
         rw [map_smul, Finsupp.smul_apply, hx j hj, smul_zero] }, fun x => Iff.rfl⟩
  have hYst : ∀ g' : G, ∀ x ∈ Y, ρ g' x ∈ Y := by
    intro g' x hx
    rw [← e.sum_repr x, map_sum]
    refine Y.sum_mem fun i _ => ?_
    rw [map_smul]
    by_cases hi : ∃ g, e i ∈ W.map (ρ g)
    · refine Y.smul_mem _ ?_
      obtain ⟨g, hg⟩ := hi
      rw [hY]
      intro j hj
      by_contra hne
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp hg
      have hmem : ρ g' (e i) ∈ W.map (ρ (g' * g)) :=
        Submodule.mem_map.mpr ⟨w, hw, by rw [map_mul ρ g' g, Module.End.mul_apply, hwe]⟩
      exact hj (g' * g) (hI _ (htr W hW (g' * g)) _ hmem j hne)
    · push_neg at hi
      rw [(hY x).mp hx i hi, zero_smul]
      exact Y.zero_mem
  have hWY : W ≤ Y := by
    intro x hx
    rw [hY]
    intro j hj
    by_contra hne
    exact hj 1 (by rw [hmap1]; exact hI W hW x hx j hne)
  have hYtop : Y = ⊤ := by
    refine (hirr Y hYst).resolve_left fun h => hWne ?_
    rw [h] at hWY
    exact le_bot_iff.mp hWY
  have hcov : ∀ j, ∃ g, e j ∈ W.map (ρ g) := by
    intro j
    by_contra hj
    push_neg at hj
    have h1 : e j ∈ Y := by
      rw [hYtop]
      exact Submodule.mem_top
    have h2 := (hY (e j)).mp h1 j hj
    rw [e.repr_self, Finsupp.single_eq_same] at h2
    exact one_ne_zero h2
  have hφe : ∀ j, ∃ c : k, c ≠ 0 ∧ ρ φ (e j) = c • e (π j) := by
    intro j
    have hv : ∀ y ∈ I, ρ y (ρ φ (e j)) = χ (π j) y • ρ φ (e j) := by
      intro y hy
      have hy' : φ⁻¹ * y * φ ∈ I :=
        (hφI _).mpr (by rwa [show φ * (φ⁻¹ * y * φ) * φ⁻¹ = y by group])
      calc ρ y (ρ φ (e j)) = ρ (y * φ) (e j) := by rw [map_mul ρ y φ, Module.End.mul_apply]
        _ = ρ (φ * (φ⁻¹ * y * φ)) (e j) := by rw [show φ * (φ⁻¹ * y * φ) = y * φ by group]
        _ = ρ φ (ρ (φ⁻¹ * y * φ) (e j)) := by
          rw [map_mul ρ φ (φ⁻¹ * y * φ), Module.End.mul_apply]
        _ = ρ φ (χ j (φ⁻¹ * y * φ) • e j) := by rw [he j _ hy']
        _ = χ (π j) y • ρ φ (e j) := by rw [map_smul, hπ j y hy]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (eigen_mem_span ρ e χ I he hsep (π j) _ hv)
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    rw [zero_smul] at hc
    exact e.ne_zero j (hinj φ (by rw [← hc, map_zero]))
  have hmemφ : ∀ x : G, ∀ j, e (π j) ∈ W.map (ρ (φ * x)) ↔ e j ∈ W.map (ρ x) := by
    intro x j
    obtain ⟨c, hc0, hc⟩ := hφe j
    constructor
    · intro h
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp h
      refine Submodule.mem_map.mpr ⟨c • w, W.smul_mem _ hw, ?_⟩
      apply hinj φ
      rw [hc, ← hwe, map_smul, map_smul, map_mul ρ φ x, Module.End.mul_apply]
    · intro h
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp h
      refine Submodule.mem_map.mpr ⟨c⁻¹ • w, W.smul_mem _ hw, ?_⟩
      rw [map_smul, map_mul ρ φ x, Module.End.mul_apply, hwe, hc, smul_smul, inv_mul_cancel₀ hc0,
        one_smul]
  have hφstep : ∀ x : G, (idx (W.map (ρ x))).image ⇑π = idx (W.map (ρ (φ * x))) := by
    intro x
    ext j'
    rw [Finset.mem_image, hidx]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hmemφ x j).mpr ((hidx _ j).mp hj)
    · intro h
      refine ⟨π.symm j', (hidx _ _).mpr ((hmemφ x _).mp ?_), π.apply_symm_apply j'⟩
      rwa [π.apply_symm_apply]
  have hpow : ∀ n : ℕ, ∀ g : G,
      (idx (W.map (ρ g))).image ⇑(π ^ n) = idx (W.map (ρ (φ ^ n * g))) := by
    intro n
    induction n with
    | zero =>
      intro g
      rw [pow_zero, pow_zero, one_mul, Equiv.Perm.coe_one, Finset.image_id]
    | succ n ih =>
      intro g
      rw [pow_succ', pow_succ', Equiv.Perm.coe_mul, ← Finset.image_image, ih, hφstep, mul_assoc]
  obtain ⟨B, hBmem⟩ : ∃ B : Finset (Finset (Fin N)), ∀ S, S ∈ B ↔ ∃ g, S = idx (W.map (ρ g)) :=
    ⟨Finset.univ.filter (fun S => ∃ g, S = idx (W.map (ρ g))), fun S => by simp⟩
  have hBcard : ∀ b ∈ B, b.card = (idx W).card := by
    intro b hb
    obtain ⟨g, rfl⟩ := (hBmem b).mp hb
    exact hcardtr W hW g
  have hBdisj : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b' := by
    intro b hb b' hb' hbb
    obtain ⟨g₁, rfl⟩ := (hBmem b).mp hb
    obtain ⟨g₂, rfl⟩ := (hBmem b').mp hb'
    rw [Finset.disjoint_left]
    intro j h1 h2
    exact hbb (hFeq g₁ g₂ j ((hidx _ j).mp h1) ((hidx _ j).mp h2))
  have hBcov : ∀ x, ∃ b ∈ B, x ∈ b := by
    intro x
    obtain ⟨g, hg⟩ := hcov x
    exact ⟨_, (hBmem _).mpr ⟨g, rfl⟩, (hidx _ x).mpr hg⟩
  have hBinv : ∀ γ : ↥(Subgroup.zpowers π), ∀ b ∈ B, b.image (fun x => γ • x) ∈ B := by
    intro γ b hb
    obtain ⟨g, rfl⟩ := (hBmem b).mp hb
    obtain ⟨n, hn⟩ : ∃ n : ℕ, π ^ n = (γ : Equiv.Perm (Fin N)) :=
      (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr γ.2)
    have hfun : (fun x => γ • x) = ⇑(π ^ n) := by
      funext x
      rw [hn]
      rfl
    rw [hfun, hpow n g]
    exact (hBmem _).mpr ⟨φ ^ n * g, rfl⟩
  obtain ⟨kk, hkc, hks⟩ := Formalism.GaloisIrreducibility.power_of_p_cycle (Fin N) π p hp hpc hcard
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ↥(Subgroup.zpowers π),
      (MulAction.toPerm g₀ : Equiv.Perm (Fin N)) = π ^ kk :=
    ⟨⟨π ^ kk, Subgroup.pow_mem _ (Subgroup.mem_zpowers π) kk⟩, Equiv.ext fun _ => rfl⟩
  rcases hB (↥(Subgroup.zpowers π)) (Fin N) B (idx W).card p g₀ hBcard hBdisj hBcov hBinv hp hcard
      (by rw [hg₀]; exact hkc) (by rw [hg₀]; exact hks) with h1 | hN
  · obtain ⟨S, hS⟩ := Finset.card_eq_one.mp h1
    have hWS : idx W = S := by
      have h3 : idx (W.map (ρ 1)) ∈ B := (hBmem _).mpr ⟨1, rfl⟩
      rw [hS, Finset.mem_singleton, hmap1] at h3
      exact h3
    have hall : ∀ j, j ∈ idx W := by
      intro j
      obtain ⟨g, hg⟩ := hcov j
      have h3 : idx (W.map (ρ g)) ∈ B := (hBmem _).mpr ⟨g, rfl⟩
      rw [hS, Finset.mem_singleton] at h3
      rw [hWS, ← h3]
      exact (hidx _ j).mpr hg
    have hcW : (idx W).card = N := by
      rw [Finset.eq_univ_of_forall hall, Finset.card_univ, Fintype.card_fin]
    have h0 := hmin W₀ hW₀ hne
    have h4 := Finset.card_le_univ (idx W₀)
    rw [Fintype.card_fin] at h4
    have hu : idx W₀ = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; omega)
    rw [Submodule.eq_top_iff']
    intro x
    apply hspan
    intro i _
    exact (hidx W₀ i).mp (by rw [hu]; exact Finset.mem_univ i)
  · exfalso
    have hbu : B.biUnion id = Finset.univ := Finset.eq_univ_of_forall fun j => by
      obtain ⟨g, hg⟩ := hcov j
      exact Finset.mem_biUnion.mpr ⟨idx (W.map (ρ g)), (hBmem _).mpr ⟨g, rfl⟩, (hidx _ j).mpr hg⟩
    have hsum : (B.biUnion id).card = B.card * (idx W).card := by
      rw [Finset.card_biUnion (by intro x hx y hy hxy; exact hBdisj x hx y hy hxy)]
      exact Finset.sum_const_nat hBcard
    rw [hbu, Finset.card_univ, hN, Fintype.card_fin] at hsum
    have hone1 : (idx W).card = 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < N) (by rw [mul_one]; exact hsum.symm)
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hone1
    have he₀ : e i₀ ∈ W := (hidx W i₀).mp (by rw [hi₀]; exact Finset.mem_singleton_self i₀)
    have hsingtr : ∀ g, ∃ j, idx (W.map (ρ g)) = {j} := fun g =>
      Finset.card_eq_one.mp (by rw [hcardtr W hW g, hone1])
    have hsame : ∀ (c c' : k) (j j' : Fin N), c' ≠ 0 → c • e j = c' • e j' → j = j' := by
      intro c c' j j' hc' h
      by_contra hjj
      have h2 := congrArg (fun v => e.repr v j') h
      simp [Finsupp.single_apply, hjj, Ne.symm hjj] at h2
      exact hc' (by first | exact h2.symm | exact h2)
    have hline : ∀ (g : G) (i : Fin N), ∃ j, ∃ c : k, c ≠ 0 ∧ ρ g (e i) = c • e j := by
      intro g i
      obtain ⟨g', hg'⟩ := hcov i
      obtain ⟨j, hj⟩ := hsingtr (g * g')
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp hg'
      have hmem : ρ g (e i) ∈ W.map (ρ (g * g')) :=
        Submodule.mem_map.mpr ⟨w, hw, by rw [map_mul ρ g g', Module.End.mul_apply, hwe]⟩
      refine ⟨j, e.repr (ρ g (e i)) j, ?_, hsing _ (htr W hW _) j hj _ hmem⟩
      intro h0
      apply e.ne_zero i
      apply hinj g
      rw [map_zero, hsing _ (htr W hW _) j hj _ hmem, h0, zero_smul]
    choose fo co hc0 hfc using hline
    have hmulf : ∀ g h i, fo (g * h) i = fo g (fo h i) := by
      intro g h i
      refine hsame (co (g * h) i) (co h i * co g (fo h i)) _ _
        (mul_ne_zero (hc0 h i) (hc0 g (fo h i))) ?_
      rw [← hfc (g * h) i, map_mul ρ g h, Module.End.mul_apply, hfc h i, map_smul, hfc g (fo h i),
        smul_smul]
    have hone : ∀ i, fo 1 i = i := fun i =>
      hsame (co 1 i) 1 _ _ one_ne_zero (by rw [← hfc 1 i, map_one, Module.End.one_apply, one_smul])
    obtain ⟨σ, hσ⟩ : ∃ σ : G →* Equiv.Perm (Fin N), ∀ g i, σ g i = fo g i :=
      ⟨{ toFun := fun g => ⟨fo g, fo g⁻¹, fun i => by rw [← hmulf, inv_mul_cancel, hone],
            fun i => by rw [← hmulf, mul_inv_cancel, hone]⟩
         map_one' := Equiv.ext fun i => hone i
         map_mul' := fun g h => Equiv.ext fun i => hmulf g h i }, fun g i => rfl⟩
    have hker1 : ∀ x ∈ H, σ x = 1 := by
      intro x hx
      refine Equiv.ext fun i => ?_
      rw [hσ, Equiv.Perm.one_apply]
      obtain ⟨g', hg'⟩ := hcov i
      obtain ⟨j, hj⟩ := hsingtr g'
      have hij : i = j := by
        have h3 := (hidx _ i).mpr hg'
        rwa [hj, Finset.mem_singleton] at h3
      subst hij
      have hd := hsing _ (htr W hW g') i hj _ (htr W hW g' x hx (e i) hg')
      exact (hsame (e.repr (ρ x (e i)) i) (co x i) i (fo x i) (hc0 x i)
        (by rw [← hfc x i]; exact hd.symm)).symm
    have hσφ : σ φ = π := by
      refine Equiv.ext fun i => ?_
      rw [hσ]
      obtain ⟨c, hc0', hc'⟩ := hφe i
      exact hsame (co φ i) c (fo φ i) (π i) hc0' (by rw [← hfc φ i, hc'])
    have horb : ∀ x, ∃ g, fo g i₀ = x := by
      intro x
      obtain ⟨g, hg⟩ := hcov x
      obtain ⟨j, hj⟩ := hsingtr g
      have hxj : x = j := by
        have h3 := (hidx _ x).mpr hg
        rwa [hj, Finset.mem_singleton] at h3
      subst hxj
      have hmem : ρ g (e i₀) ∈ W.map (ρ g) := Submodule.mem_map.mpr ⟨e i₀, he₀, rfl⟩
      have hd := hsing _ (htr W hW g) x hj _ hmem
      exact ⟨g, (hsame (e.repr (ρ g (e i₀)) x) (co g i₀) x (fo g i₀) (hc0 g i₀)
        (by rw [← hfc g i₀]; exact hd.symm)).symm⟩
    letI : MulAction (G ⧸ H) (Fin N) := MulAction.compHom (Fin N) (QuotientGroup.lift H σ (by
      intro x hx
      first
      | exact hker1 x hx
      | exact (MonoidHom.mem_ker).mpr (hker1 x hx)))
    have htrans : MulAction.IsPretransitive (G ⧸ H) (Fin N) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨gx, rfl⟩ := horb x
      obtain ⟨gy, rfl⟩ := horb y
      refine ⟨((gy * gx⁻¹ : G) : G ⧸ H), ?_⟩
      show σ (gy * gx⁻¹) (fo gx i₀) = fo gy i₀
      rw [hσ, ← hmulf, mul_assoc, inv_mul_cancel, mul_one]
    obtain ⟨g₁, hg₁⟩ : ∃ g₁ : G ⧸ H, (MulAction.toPerm g₁ : Equiv.Perm (Fin N)) = π ^ kk := by
      refine ⟨((φ ^ kk : G) : G ⧸ H), Equiv.ext fun x => ?_⟩
      show σ (φ ^ kk) x = (π ^ kk) x
      rw [map_pow, hσφ]
    exact (hJ (G ⧸ H) (Fin N) p g₁ htrans hp hcard (by simpa using hp3)
      (by rw [hg₁]; exact hkc) (by rw [hg₁]; exact hks)).2 hsolv
end Formalism.CyclotomicNorms
