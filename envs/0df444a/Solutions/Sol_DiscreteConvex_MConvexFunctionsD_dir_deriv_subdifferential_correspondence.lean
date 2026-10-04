-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.dir_deriv_subdifferential_correspondence
-- status  : ACCEPTED   (disprove)
-- author  : @sometik179
-- created : 2026-10-02T16:32:51.070983+00:00
-- url     : https://prove2.me/submissions/4c2bc56f-5484-46a2-bd8f-6138d9a4cc41

import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_GammaHat
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SubDifferential
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SubDifferentialR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open DiscreteConvex.MConvexFunctionsD
open Classical
open scoped BigOperators

namespace DisconnectedExchange

def domain (x : Bool → ℝ) : Prop :=
  (0 < x false ∧ x false < 1 ∧ x false + x true = 0) ∨
  (2 < x false ∧ x false < 3 ∧ x false + x true = 1)

noncomputable def f (x : Bool → ℝ) : WithTop ℝ := if domain x then 0 else ⊤

def shift (x : Bool → ℝ) (a : ℝ) : Bool → ℝ :=
  fun b => if b then x true - a else x false + a

lemma mem_dom (x : Bool → ℝ) : x ∈ DomR f ↔ domain x := by
  classical
  simp only [DomR, Set.mem_setOf_eq, f]
  split_ifs <;> simp_all

lemma segment_radius (l r s : ℝ) (x : Bool → ℝ)
    (hx : l < x false ∧ x false < r ∧ x false + x true = s) :
    ∃ e : ℝ, 0 < e ∧ ∀ a : ℝ, |a| ≤ e →
      l < shift x a false ∧ shift x a false < r ∧
        shift x a false + shift x a true = s := by
  refine ⟨min (x false - l) (r - x false) / 2, ?_, ?_⟩
  · exact div_pos (lt_min (by linarith [hx.1]) (by linarith [hx.2.1])) (by norm_num)
  · intro a ha
    have hab := abs_le.mp ha
    have hleft := min_le_left (x false - l) (r - x false)
    have hright := min_le_right (x false - l) (r - x false)
    simp only [shift, Bool.false_eq_true, ↓reduceIte]
    constructor
    · linarith [hx.1]
    constructor
    · linarith [hx.2.1]
    · linarith [hx.2.2]

lemma local_radius (x : Bool → ℝ) (hx : domain x) :
    ∃ e : ℝ, 0 < e ∧ ∀ a : ℝ, |a| ≤ e → domain (shift x a) := by
  rcases hx with hx | hx
  · obtain ⟨e, he, h⟩ := segment_radius 0 1 0 x hx
    exact ⟨e, he, fun a ha => Or.inl (h a ha)⟩
  · obtain ⟨e, he, h⟩ := segment_radius 2 3 1 x hx
    exact ⟨e, he, fun a ha => Or.inr (h a ha)⟩

lemma antitone (x y : Bool → ℝ) (hx : domain x) (hy : domain y)
    (u : Bool) (hu : y u < x u) : x (!u) < y (!u) := by
  cases u <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp only [Bool.not_false, Bool.not_true] <;> linarith [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]

lemma exchange : MExchangeAxiomR f := by
  intro x hx y hy u hu
  have hxD := (mem_dom x).mp hx
  have hyD := (mem_dom y).mp hy
  have hv := antitone x y hxD hyD u hu
  obtain ⟨ex, hex, hxx⟩ := local_radius x hxD
  obtain ⟨ey, hey, hyy⟩ := local_radius y hyD
  refine ⟨!u, hv, min ex ey, lt_min hex hey, ?_⟩
  intro a ha ham
  have hax : |a| ≤ ex := by rw [abs_of_nonneg ha]; exact ham.trans (min_le_left _ _)
  have hay : |a| ≤ ey := by rw [abs_of_nonneg ha]; exact ham.trans (min_le_right _ _)
  have hxn := hxx (-a) (by simpa using hax)
  have hxp := hxx a hax
  have hyn := hyy (-a) (by simpa using hay)
  have hyp := hyy a hay
  have hdx : domain (fun w => x w - a * (CharVec u w - CharVec (!u) w : ℝ)) := by
    cases u
    · convert hxn using 1
      funext w; cases w <;> simp [shift, CharVec] <;> ring
    · convert hxp using 1
      funext w; cases w <;> simp [shift, CharVec] <;> ring
  have hdy : domain (fun w => y w + a * (CharVec u w - CharVec (!u) w : ℝ)) := by
    cases u
    · convert hyp using 1
      funext w; cases w <;> simp [shift, CharVec] <;> ring
    · convert hyn using 1
      funext w; cases w <;> simp [shift, CharVec] <;> ring
  simp [f, hxD, hyD, hdx, hdy]


lemma derivative_nonnegative (x d : Bool → ℝ) (hx : domain x) : 0 ≤ DirDeriv f x d := by
  have hx0 : f x = 0 := by simp [f, hx]
  have hne : {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
      L = PosScalarMul (1 / t) (f (fun v => x v + t * d v) - f x)}.Nonempty :=
    ⟨_, 1, by norm_num, rfl⟩
  unfold DirDeriv
  apply le_csInf hne
  rintro L ⟨t, ht, rfl⟩
  rw [hx0, sub_zero]
  unfold f
  split_ifs <;> simp [PosScalarMul, ne_of_gt ht]

end DisconnectedExchange
open DisconnectedExchange

-- prove2me-proof-type: disprove

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ f : (V → ℝ) → WithTop ℝ, MExchangeAxiomR f → ∀ x ∈ DomR f,
      TriangleInequality (fun u v => DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ))) ∧
      SubDifferentialR f x =
        AdmissiblePotentials (fun u v => DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ))) ∧
      (SubDifferentialR f x).Nonempty ∧
      (∀ d : V → ℝ, DirDeriv f x d =
        GammaHat (fun u v => DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ))) d)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MExchangeAxiom f → ∀ x ∈ DomZ f,
      TriangleInequality (fun u v => f (fun w => x w - CharVec u w + CharVec v w) - f x) ∧
      SubDifferential f x =
        AdmissiblePotentials (fun u v => f (fun w => x w - CharVec u w + CharVec v w) - f x) ∧
      (SubDifferential f x).Nonempty)) := by
  intro H
  let x : Bool → ℝ := fun b => if b then -(1/2 : ℝ) else 1/2
  let y : Bool → ℝ := fun b => if b then -(3/2 : ℝ) else 5/2
  have hxD : domain x := by norm_num [domain, x]
  have hyD : domain y := by norm_num [domain, y]
  have hx : x ∈ DomR f := (mem_dom x).mpr hxD
  have heq := ((H (V := Bool)).1 f exchange x hx).2.1
  have hp : (fun _ : Bool => (1 : ℝ)) ∈ SubDifferentialR f x := by
    rw [heq]
    intro u v huv
    simpa using derivative_nonnegative x (fun w => (CharVec v w - CharVec u w : ℝ)) hxD
  have hbad := hp y
  norm_num [f, hxD, hyD, Fintype.sum_bool, x, y] at hbad
  have : (1 : ℝ) ≤ 0 := WithTop.coe_le_coe.mp hbad
  linarith

#print axioms solution
