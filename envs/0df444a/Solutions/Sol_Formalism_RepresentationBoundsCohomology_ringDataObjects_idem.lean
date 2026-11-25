-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:17.656917+00:00
-- url     : https://prove2.me/submissions/882528d9-f260-42b5-b844-e79709f81905

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_blk_mul
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_diag_mul
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_r_mem
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_rank_diag_ite
import Theorems.Thm_Formalism_NG_idemLift
import Theorems.Thm_Formalism_NG_rankMod
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_burnsideMat
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_charT
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_cornerIdem
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_idemSmall
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_nilConst
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_rankConst
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_satur


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
set_option maxHeartbeats 1000000
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : StatIdem := by
  intro O _ _ _ _ X _ T d _ _ G _ r π t bl χ₁ ε hP hirr hcard0
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  let R := spanSub T r
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have huniq : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hab
    have hs : Subsingleton {x // bl x = bl a} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 _ ha))
    exact congrArg Subtype.val (hs.elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)
  have hBD : ∀ a ∈ tSpan T r, ∀ i j, bl i ≠ bl j → a π i j = 0 := by
    rintro a ⟨s, c, hc, rfl⟩ i j hij
    simp [Finset.sum_apply, Matrix.sum_apply, hbd _ i j hij]
  let n0 := {a // bl a = 0}
  let ι := {a // bl a ≠ 0}
  let Φ : R →+* Matrix n0 n0 O × (ι → O) :=
    { toFun := fun a => ((a.1 π).toSquareBlock bl 0, fun i => a.1 π i.1 i.1)
      map_one' := by
        refine Prod.ext ?_ ?_
        · ext i j
          by_cases h : i = j
          · subst h; simp [Matrix.toSquareBlock_def]
          · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
            simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
        · funext i
          simp
      map_mul' := fun a b => Prod.ext (blk_mul bl (hBD a.1 a.2) 0)
        (funext fun i => diag_mul bl (hBD a.1 a.2) i.1 (fun l hl => huniq _ _ i.2 hl))
      map_zero' := by
        refine Prod.ext ?_ ?_
        · ext i j; simp [Matrix.toSquareBlock_def]
        · funext i; simp
      map_add' := fun a b => by
        refine Prod.ext ?_ ?_
        · ext i j; simp [Matrix.toSquareBlock_def]
        · funext i; simp }
  let f₀ : R →+* Matrix n0 n0 k × (ι → k) :=
    (RingHom.prodMap res.mapMatrix (RingHom.compLeft res ι)).comp Φ
  have hf1 : ∀ (a : R) i j, (f₀ a).1 i j = res (a.1 π i.1 j.1) := fun a i j => rfl
  have hf2 : ∀ (a : R) i, (f₀ a).2 i = res (a.1 π i.1 i.1) := fun a i => rfl
  have hsm : ∀ (c : O) (a : R), f₀ (c • a) = res c • f₀ a := by
    intro c a
    refine Prod.ext ?_ ?_
    · ext i j
      rw [hf1]
      simp [hf1]
    · funext i
      rw [hf2]
      simp [hf2]
  let B' : Subalgebra k (Matrix n0 n0 k × (ι → k)) :=
    { toSubsemiring := f₀.rangeS
      algebraMap_mem' := fun c => by
        obtain ⟨c0, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨c0 • (1 : R), ?_⟩
        rw [hsm, map_one, Algebra.algebraMap_eq_smul_one] }
  have hB' : ∀ z, z ∈ B' ↔ ∃ a, f₀ a = z := fun z => Iff.rfl
  obtain ⟨i0⟩ : Nonempty n0 := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hcard0)
  have : Nonempty n0 := ⟨i0⟩
  let rR : G →* R :=
    { toFun := fun g => ⟨r g, r_mem T r g⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun g h => Subtype.ext (map_mul r g h) }
  let ρb : G →* Matrix n0 n0 k := (((RingHom.fst _ _).comp f₀).toMonoidHom).comp rR
  have hb : Submodule.span k (Set.range ρb) = ⊤ := burnsideMat k n0 G ρb hirr
  have hsurj : ∀ A : Matrix n0 n0 k, ∃ z ∈ B', z.1 = A := by
    intro A
    have hA : A ∈ Submodule.span k (Set.range ρb) := hb ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨f₀ (rR g), ⟨rR g, rfl⟩, rfl⟩
    | zero => exact ⟨0, B'.zero_mem, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb', rfl⟩ := hy
      exact ⟨a + b, B'.add_mem ha hb', rfl⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨c • a, B'.smul_mem ha c, rfl⟩
  have hcor := cornerIdem k n0 ι B' hcard0 hsurj
  obtain ⟨u1, hu1⟩ := (hB' _).mp (hcor 1)
  obtain ⟨u2, hu2⟩ := (hB' _).mp (hcor (Matrix.single i0 i0 1))
  have hv1 : f₀ (1 - u1) = (0, 1) := by
    rw [map_sub, map_one, hu1]
    refine Prod.ext ?_ ?_ <;> simp
  have hfin : Module.Finite O R :=
    (inferInstance : Module.Finite O (Subalgebra.toSubmodule R))
  let f := f₀.rangeRestrict
  have hfs : Function.Surjective f := f₀.rangeRestrict_surjective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨N, hN⟩ := satur O (X → Matrix d d O) (Subalgebra.toSubmodule R)
  have h5 : ∀ a ∈ IsLocalRing.maximalIdeal O • Subalgebra.toSubmodule R,
      ∃ w : R, w ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O R) ∧ w.1 = a := by
    intro a ha
    induction ha using Submodule.smul_induction_on' with
    | smul c hc m hm => exact ⟨c • ⟨m, hm⟩, Submodule.smul_mem_smul hc Submodule.mem_top, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨w', hw', rfl⟩ := hb
      exact ⟨w + w', Submodule.add_mem _ hw hw', rfl⟩
  have hker : ∀ x : R, f x = 0 →
      ∃ n : ℕ, x ^ n ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O R) := by
    intro x hx
    have hx0 : f₀ x = 0 := congrArg Subtype.val hx
    have hπ : (x.1 π).map res = 0 := by
      ext i j
      by_cases hij : bl i = bl j
      · by_cases hi : bl i = 0
        · exact congrFun (congrFun (congrArg Prod.fst hx0) ⟨i, hi⟩) ⟨j, hij ▸ hi⟩
        · have hh := huniq i j hi hij
          subst hh
          exact congrFun (congrArg Prod.snd hx0) ⟨i, hi⟩
      · simp [hBD x.1 x.2 i j hij]
    have hnil := nilConst O X T d hloc x.1 (charT O X T d G r hG1 x.1 x.2) π hπ
    have hdiv : ∀ y i j, ∃ c, ((x.1 y) ^ Fintype.card d) i j = ϖ * c := by
      intro y i j
      have h1 : res (((x.1 y) ^ Fintype.card d) i j) = 0 := congrFun (congrFun (hnil y) i) j
      have h2 : ((x.1 y) ^ Fintype.card d) i j ∈ IsLocalRing.maximalIdeal O :=
        (IsLocalRing.residue_eq_zero_iff _).mp h1
      rw [hmax, Ideal.mem_span_singleton] at h2
      exact h2
    choose c hc using hdiv
    let y : X → Matrix d d O := fun z => Matrix.of (c z)
    have hxy : x.1 ^ Fintype.card d = ϖ • y := by
      funext z; ext i j
      simp [y, hc]
    refine ⟨Fintype.card d * N, ?_⟩
    have h3 : x.1 ^ (Fintype.card d * N) ∈
        (IsLocalRing.maximalIdeal O) ^ N • (⊤ : Submodule O (X → Matrix d d O)) := by
      rw [pow_mul, hxy, smul_pow]
      exact Submodule.smul_mem_smul
        (Ideal.pow_mem_pow (hmax ▸ Ideal.mem_span_singleton_self ϖ) N) Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := h5 _ (hN (x.1 ^ (Fintype.card d * N)) (R.pow_mem x.2 _) h3)
    have hwx : w = x ^ (Fintype.card d * N) := Subtype.ext hwe
    rw [← hwx]; exact hw
  have hi1 : IsIdempotentElem (f (1 - u1)) := Subtype.ext (by
    show f₀ (1 - u1) * f₀ (1 - u1) = f₀ (1 - u1)
    rw [hv1]; refine Prod.ext ?_ ?_ <;> simp)
  have hi2 : IsIdempotentElem (f u2) := Subtype.ext (by
    show f₀ u2 * f₀ u2 = f₀ u2
    rw [hu2]; refine Prod.ext ?_ ?_ <;> simp)
  have h12 : f (1 - u1) * f u2 = 0 := Subtype.ext (by
    show f₀ (1 - u1) * f₀ u2 = 0
    rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)
  have h21 : f u2 * f (1 - u1) = 0 := Subtype.ext (by
    show f₀ u2 * f₀ (1 - u1) = 0
    rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)
  obtain ⟨E₁, E₂, hE1, hE2, hE12, hE21, hfE1, hfE2⟩ :=
    idemLift O R f₀.range f hfs hker _ _ hi1 hi2 h12 h21
  have hg1 : f₀ E₁ = (0, 1) := (congrArg Subtype.val hfE1).trans hv1
  have hg2 : f₀ E₂ = (Matrix.single i0 i0 1, 0) := (congrArg Subtype.val hfE2).trans hu2
  have hΦ1 : Φ E₁ * Φ E₁ = Φ E₁ := by rw [← map_mul, hE1.eq]
  have hΦ2 : Φ E₂ * Φ E₂ = Φ E₂ := by rw [← map_mul, hE2.eq]
  have hb1 : (Φ E₁).1 = 0 :=
    idemSmall O n0 (Φ E₁).1 (congrArg Prod.fst hΦ1) (congrArg Prod.fst hg1)
  have hd1 : ∀ i : ι, E₁.1 π i.1 i.1 = 1 := by
    intro i
    have h1 : IsIdempotentElem (E₁.1 π i.1 i.1) := congrFun (congrArg Prod.snd hΦ1) i
    have h2 : res (E₁.1 π i.1 i.1) = 1 := congrFun (congrArg Prod.snd hg1) i
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h
    · rw [h, map_zero] at h2; exact absurd h2 zero_ne_one
    · exact h
  have hd2 : ∀ i : ι, E₂.1 π i.1 i.1 = 0 := by
    intro i
    have h1 : IsIdempotentElem (E₂.1 π i.1 i.1) := congrFun (congrArg Prod.snd hΦ2) i
    have h2 : res (E₂.1 π i.1 i.1) = 0 := congrFun (congrArg Prod.snd hg2) i
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h
    · exact h
    · rw [h, map_one] at h2; exact absurd h2 one_ne_zero
  have heB : E₁.1 π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1) := by
    ext i j
    by_cases hij : bl i = bl j
    · by_cases hi : bl i = 0
      · have h1 : E₁.1 π i j = 0 := congrFun (congrFun hb1 ⟨i, hi⟩) ⟨j, hij ▸ hi⟩
        rw [h1]
        by_cases hh : i = j
        · subst hh; simp [hi]
        · rw [Matrix.diagonal_apply_ne _ hh]
      · have hh := huniq i j hi hij
        subst hh
        rw [hd1 ⟨i, hi⟩]; simp [hi]
    · rw [hBD E₁.1 E₁.2 i j hij, Matrix.diagonal_apply_ne _ (fun h => hij (congrArg bl h))]
  have he1 : ∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → E₂.1 π a b = 0 := by
    intro a b hab
    by_cases hij : bl a = bl b
    · have ha : bl a ≠ 0 := by
        rcases hab with h | h
        · exact h
        · rw [hij]; exact h
      have hh := huniq a b ha hij
      subst hh
      exact hd2 ⟨a, ha⟩
    · exact hBD E₂.1 E₂.2 a b hij
  have hcardι : Fintype.card {a // bl a ≠ 0} = t := by
    have hbij : Function.Bijective
        (fun a : {a // bl a ≠ 0} => (⟨bl a.1, a.2⟩ : {c : Fin (t + 1) // c ≠ 0})) := by
      constructor
      · intro a b hab
        exact Subtype.ext (huniq a.1 b.1 a.2 (congrArg Subtype.val hab))
      · intro c
        obtain ⟨a⟩ : Nonempty {a // bl a = c.1} :=
          Fintype.card_pos_iff.mp (by rw [hc1 c.1 c.2]; norm_num)
        exact ⟨⟨a.1, by rw [a.2]; exact c.2⟩, Subtype.ext a.2⟩
    rw [Fintype.card_of_bijective hbij]
    simp [Fintype.card_subtype_compl]
  have hrB : ((E₁.1 π).map (algebraMap O (FractionRing O))).rank = t := by
    have h1 : (E₁.1 π).map (algebraMap O (FractionRing O)) =
        Matrix.diagonal fun a => if bl a ≠ 0 then (1 : FractionRing O) else 0 := by
      rw [heB]
      ext i j
      by_cases hh : i = j
      · subst hh
        by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hh]
    rw [h1, rank_diag_ite, Nat.card_eq_fintype_card]
    convert hcardι
  have hr1 : ((E₂.1 π).map (algebraMap O (FractionRing O))).rank = 1 := by
    rw [← rankMod O d (E₂.1 π) (congrFun (congrArg Subtype.val hE2.eq) π)]
    have h1 : (E₂.1 π).map (IsLocalRing.residue O) =
        Matrix.diagonal fun a => if a = i0.1 then (1 : k) else 0 := by
      ext i j
      by_cases hi : bl i = 0 ∧ bl j = 0
      · have h2 : res (E₂.1 π i j) = Matrix.single i0 i0 (1 : k) ⟨i, hi.1⟩ ⟨j, hi.2⟩ :=
          congrFun (congrFun (congrArg Prod.fst hg2) ⟨i, hi.1⟩) ⟨j, hi.2⟩
        show res (E₂.1 π i j) = _
        rw [h2, Matrix.single_apply, Matrix.diagonal_apply]
        by_cases h3 : i = i0.1
        · by_cases h4 : j = i0.1
          · subst h3; subst h4; simp
          · have : ¬ (i0 = ⟨j, hi.2⟩) := fun e => h4 (congrArg Subtype.val e).symm
            have h5 : i ≠ j := fun e => h4 (e ▸ h3)
            simp [this, h5]
        · have : ¬ (i0 = ⟨i, hi.1⟩) := fun e => h3 (congrArg Subtype.val e).symm
          simp [this, h3]
      · have h2 : E₂.1 π i j = 0 := he1 i j (by
          by_contra hcon
          push Not at hcon
          exact hi hcon)
        show res (E₂.1 π i j) = _
        rw [h2, map_zero, Matrix.diagonal_apply]
        by_cases h3 : i = j
        · subst h3
          have : i ≠ i0.1 := fun e => hi ⟨e ▸ i0.2, e ▸ i0.2⟩
          simp [this]
        · simp [h3]
    rw [h1, rank_diag_ite, Nat.card_eq_fintype_card]
    simp
  refine ⟨E₁.1, E₂.1, E₁.2, E₂.2, congrArg Subtype.val hE1.eq, congrArg Subtype.val hE2.eq,
    congrArg Subtype.val hE12, congrArg Subtype.val hE21, fun x => ?_, fun x => ?_, heB, he1⟩
  · rw [rankConst O X T d hloc E₁.1 (congrArg Subtype.val hE1.eq)
      (charT O X T d G r hG1 E₁.1 E₁.2) x π, hrB]
  · rw [rankConst O X T d hloc E₂.1 (congrArg Subtype.val hE2.eq)
      (charT O X T d G r hG1 E₂.1 E₂.2) x π, hr1]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
