-- Prove2me | solution 1 for BirkhoffGlobalSection.compact_unique_fiber_selection_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:02:33.010983+00:00
-- url     : https://prove2.me/submissions/8a8f7b8a-9f1e-4c27-bdee-541d02e525b0

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact

open BirkhoffGlobalSection

theorem solution
    (G : Set ({x : Phase // x ∈ unitThreeSphere} × ℝ))
    (hcompact : IsCompact G)
    (hunique : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∃! r : ℝ, (x, r) ∈ G) :
    Continuous (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      Classical.choose (hunique x).exists) := by
  letI : CompactSpace G := isCompact_iff_compactSpace.mp hcompact
  let p : G → {x : Phase // x ∈ unitThreeSphere} := fun z => z.val.1
  have hpcont : Continuous p :=
    continuous_fst.comp continuous_subtype_val
  have hpbij : Function.Bijective p := by
    constructor
    · intro a b hab
      change a.val.1 = b.val.1 at hab
      apply Subtype.ext
      apply Prod.ext
      · exact hab
      · have ha : (a.val.1, a.val.2) ∈ G := a.property
        have hb : (b.val.1, b.val.2) ∈ G := b.property
        have hb' : (a.val.1, b.val.2) ∈ G := by
          simpa only [← hab] using hb
        exact (hunique a.val.1).unique ha hb'
    · intro x
      obtain ⟨r, hr⟩ := (hunique x).exists
      exact ⟨⟨(x, r), hr⟩, rfl⟩
  let e : G ≃ {x : Phase // x ∈ unitThreeSphere} :=
    Equiv.ofBijective p hpbij
  have hecont : Continuous e := hpcont
  have heinv : Continuous e.symm :=
    hecont.continuous_symm_of_equiv_compact_to_t2
  have hselect : ∀ x : {x : Phase // x ∈ unitThreeSphere},
      (e.symm x).val.2 = Classical.choose (hunique x).exists := by
    intro x
    have hfirst : (e.symm x).val.1 = x := by
      have h := e.apply_symm_apply x
      exact h
    have hmem : (x, (e.symm x).val.2) ∈ G := by
      have hp : (x, (e.symm x).val.2) = (e.symm x).val := by
        apply Prod.ext
        · exact hfirst.symm
        · rfl
      rw [hp]
      exact (e.symm x).property
    exact (hunique x).unique hmem (Classical.choose_spec (hunique x).exists)
  have hcont : Continuous (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      (e.symm x).val.2) :=
    (continuous_snd.comp continuous_subtype_val).comp heinv
  have hfun : (fun x : {x : Phase // x ∈ unitThreeSphere} =>
      (e.symm x).val.2) =
      (fun x => Classical.choose (hunique x).exists) := by
    funext x
    exact hselect x
  rw [← hfun]
  exact hcont
