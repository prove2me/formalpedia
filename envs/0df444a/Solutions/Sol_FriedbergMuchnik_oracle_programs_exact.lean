-- Prove2me | solution 1 for FriedbergMuchnik.oracle_programs_exact
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T20:04:10.556317+00:00
-- url     : https://prove2.me/submissions/f4ba555a-7a54-43d0-84bb-ab519f11109b

import Definitions.Def_FriedbergMuchnik_Priority

open FriedbergMuchnik

theorem solution (O f : ℕ →. ℕ) :
    RecursiveIn {O} f ↔ ∃ c : Program, oracleEval O c = f := by
  rw [RecursiveIn.iff_nat]
  constructor
  · intro h
    induction h with
    | zero =>
        refine ⟨.mu .right, ?_⟩
        funext n
        apply Part.eq_some_iff.mpr
        simp only [oracleEval, Nat.unpair_pair]
        apply Nat.mem_rfind.mpr
        exact ⟨by simp, fun hm => (Nat.not_lt_zero _ hm).elim⟩
    | succ => exact ⟨.succ, rfl⟩
    | left => exact ⟨.left, rfl⟩
    | right => exact ⟨.right, rfl⟩
    | oracle g hg =>
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨.query, rfl⟩
    | pair hf hg ihf ihg =>
        rcases ihf with ⟨cf, rfl⟩
        rcases ihg with ⟨cg, rfl⟩
        exact ⟨.pair cf cg, rfl⟩
    | comp hf hg ihf ihg =>
        rcases ihf with ⟨cf, rfl⟩
        rcases ihg with ⟨cg, rfl⟩
        exact ⟨.comp cf cg, rfl⟩
    | prec hf hg ihf ihg =>
        rcases ihf with ⟨cf, rfl⟩
        rcases ihg with ⟨cg, rfl⟩
        exact ⟨.prec cf cg, rfl⟩
    | rfind hf ih =>
        rcases ih with ⟨cf, rfl⟩
        exact ⟨.mu cf, rfl⟩
  · rintro ⟨c, rfl⟩
    induction c with
    | query => exact .oracle _ (Set.mem_singleton _)
    | succ => exact .succ
    | left => exact .left
    | right => exact .right
    | pair cf cg ihf ihg => exact .pair ihf ihg
    | comp cf cg ihf ihg => exact .comp ihf ihg
    | prec cf cg ihf ihg => exact .prec ihf ihg
    | mu cf ih => exact .rfind ih
